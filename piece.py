"""A parser for uncompressed MuseScore2 files (\*.mscx)

"""

import os,tempfile,subprocess,re
from bs4 import BeautifulSoup, NavigableString
from fractions import Fraction
from copy import copy
try:
  from IPython.display import Image,display
except ImportError:
    raise NoIPython("IPython is not installed.  Won't display image output of Piece.get()")


# conversion dictionary
durations = {"measure" : 1.0, "whole" : 1/1,
 "half" : 1/2, "quarter" : 1/4, "eighth" : 1/8, "16th" : 1/16, "32nd" : 1/32,
 "64th" : 1/64, "128th" : 1/128}

skip_tags = ['Harmony','Slur','Tempo','Tuplet','Beam','endSpanner','HairPin','Volta','Trill','Dynamic'] # Tags that can stand between a <Harmony> and the event it is attached to
grace_tags = ['acciaccatura','appoggiatura','grace4','grace4after','grace8','grace8after','grace16','grace16after','grace32','grace32after','grace64','grace64after']

regex = r"""(^(\.)?((?P<key>[a-gA-G](b*|\#*)|(b*|\#*)(VII|VI|V|IV|III|II|I|vii|vi|v|iv|iii|ii|i))\.)?((?P<pedal>(b*|\#*)(VII|VI|V|IV|III|II|I|vii|vi|v|iv|iii|ii|i))\[)?(?P<numeral>(b*|\#*)(VII|VI|V|IV|III|II|I|vii|vi|v|iv|iii|ii|i|Ger|It|Fr))(?P<form>[%o+M])?(?P<figbass>(9|7|65|43|42|2|64|6))?(\((?P<changes>(\+?(b*|\#*)\d)+)\))?(/\.?(?P<relativeroot>(b*|\#*)(VII|VI|V|IV|III|II|I|vii|vi|v|iv|iii|ii|i)))?(?P<pedalend>\])?(?P<phraseend>\\\\)?$|@none)"""

tonal_pc =  {# complete MuseScore system: https://musescore.org/en/plugin-development/tonal-pitch-class-enum
                "13": "F",
                "15": "G",
                "19": "b"
            }
empty = """
<museScore version="2.06">
  <programVersion>2.3.2</programVersion>
  <programRevision>3543170</programRevision>
  <Score>
    <LayerTag id="0" tag="default"></LayerTag>
    <currentLayer>0</currentLayer>
    <Division>480</Division>
    <Style>
      <showMeasureNumberOne>1</showMeasureNumberOne>
      <harmonyY>5</harmonyY>
    </Style>
    <showInvisible>1</showInvisible>
    <showUnprintable>1</showUnprintable>
    <showFrames>1</showFrames>
    <showMargins>0</showMargins>
    <Part>
      <Staff id="1">
        <StaffType group="pitched">
          <name>stdNormal</name>
          </StaffType>
        <bracket type="1" span="2"/>
        <barLineSpan>2</barLineSpan>
        </Staff>
      <Staff id="2">
        <StaffType group="pitched">
          <name>stdNormal</name>
          </StaffType>
        <defaultClef>F</defaultClef>
        <bracket type="-1" span="0"/>
        <barLineSpan>0</barLineSpan>
        </Staff>
      </Part>
 <Staff id="1">
 </Staff>
 <Staff id="2">
</Staff>
</Score>
</museScore>
"""

maj = ['I','II','III','IV','V','VI','VII']
min = ['i','ii','iii','iv','v','vi','vii']
shifts =    [[0,0,0,0,0,0,0],
            [0,0,1,0,0,0,1],
            [0,1,1,0,0,1,1],
            [0,0,0,-1,0,0,0],
            [0,0,0,0,0,0,1],
            [0,0,1,0,0,1,1],
            [0,1,1,0,1,1,1]]

def appl(n,k,global_minor=False):
    """Returns the absolute key of an applied chord, given the local key.

    Parameters
    ----------
    n : str
        The key that the chord is applied to.
    k : str
        The local key, i.e. the tonal context where the applied chord appears.
    global_minor : bool
        Has to be set to true if k is to be interpreted in a minor context.

    Example
    -------
    If the label viio6/V appears in the context of the key of bVI,
    viio6 pertains to the absolute key bIII.

    >>> appl("V","bVI")
    'bIII'

    """

    shift = n.count('#') - n.count('b') + k.count('#') - k.count('b')
    for char in "#b":
        n = n.replace(char,'')
        k = k.replace(char,'')
    steps = maj if n.isupper() else min
    i = steps.index(n)
    j = maj.index(k.upper())
    step = steps[(i+j)%7]
    if k.islower() and i in [2,5,6]:
        shift -= 1
    if global_minor:
        j = (j-2)%7
    shift += shifts[i][j]
    acc = shift * '#' if shift > 0 else -shift * 'b'
    return acc+step


def measure_decimal(m,b,timesig='4/4',decimals=1):
    """Converts a measure number and and a beat to one float.

    A full measure is normalised to 1. so that beat 1 of measure m is m.0,
    the middle beat is m.5 etc. The function calls beat2float() for beat conversion,
    which lives in piece.py

    Parameters:
    -----------

    m: number
        Measure number
    b: str
        Beat in the shape beat.subbeatFraction
    timesig: str
        Time signature. Default: '4/4'
    decimals: int
        Number of decimals the resulting float is rounded to.

    Example:
    --------

    >>> measure_decimal(56,'3.2/3','3/4',2)
    56.89

    """
    m = float(m)
    b = beat2float(b)
    spl = timesig.split('/')
    t = int(spl[0]) #if all beats are quarter beats, change this line to
    # t = int(Fraction(timesig)*4)
    if t == 2: #in the case that /8 = eights beats, /4 & /2 = quarter beats, if /2 = half beats, delete this line
        t = 2 * t
    b = (b-1)/t
    return round(m+b,decimals)


def get_sibling(n,next=True):
    """Returns a sibling of a XML node

    This function is needed because in Beautifulsoup, the siblings often are
    empty strings between two tags. Returns None if there is no sibling.

    Parameters
    ----------

    n: bs4.element.Tag
        The node to fetch the sibling from.
    next: bool, optional
        Pass False to get the previous sibling
    """
    if next:
        if isinstance(n.next_sibling, NavigableString):
            return n.next_sibling.next_sibling
        else:
            return n.next_sibling
    else:
        if isinstance(n.previous_sibling, NavigableString):
            return n.previous_sibling.previous_sibling
        else:
            return n.previous_sibling


def get_meta(annotations):
    """Reads the metadata at the beginning of annotation TXT files

    Returns a dictionary with values of all leading lines that have the shape
    ``@key: value``, such as ``@meter: 4/4``

    Parameters
    ----------

    annotations: str
        Path to the TXT file
    """
    with open(annotations,'r') as file:
        line = file.readline()
        meta = {}
        while line[0] == '@':
            lst = line.strip().split(': ')
            meta[lst[0]] = lst[1]
            line = file.readline()
    return meta

def beat2float(beat):
    """Converts a beat in the form ``2.1/3`` to a float
    """
    if isinstance(beat,float):
        return beat
    beat = str(beat)
    split = beat.split('.')
    val = float(split[0])
    if len(split) > 1:
        val += float(Fraction(split[1]))
    return val


class Piece():
    """A Piece() instance represents a MSCX file's document structure.

    The information included in the score can be easily accessed and manipulated,
    notably harmony annotation labels.

    Attributes
    ----------
    source: str
        Full path to the MSCX file
    dir: str
        Directory path of the MSCX file
    piece: str
        Filename to the MSCX file
    soup: bs4.BeautifulSoup
        bs4 object holding the documents XML structure. This is what has to be manipulated
        to change the MSCX file that is written by the dump() function. The general way to
        manipulate is by changing the tags which are represented in the ``measure`` dictionary.
    repair: bool
        Call dump() if corrections are made
    mscore: str
        MuseScore2 executable
    tsm_only: bool
        True if object is intialized with timesig_map_only=True
    measure: dict
        Dictionary holding information about each measure, including references to the tags.
        This dictionary can be called by hashing the Piece object, e.g. ``p[13]``
    key: str
        Key of the piece as inferred from the first harmony label.
    keysig: str
        Number of accidentals as string, e.g. "-2" for bb or "3" for ###
    len: int
        Length of the piece in ticks (quarter note = 480 ticks, whole note = 1920 ticks)
    tuplets: dict
        Dictionary with id: tuplet fraction, e.g. ``{"1": Fraction(7/4)}``
    volta_measures: list
        Holds references to the measures under a first volta which sometimes have to be
        excluded or included in measure counts.
    firststaff: bs4.element.Tag
        Reference to the node holding the measures of the upper staff.
    otherstaves: list
        List holding references to the other staff tags.

    Examples
    --------

    The piece's information is stored in the ``measure`` dictionary. Therfore, you can
    hash the object directly instead. Keys are the measure numbers. Pickup measures have
    number 0.::

        >>> p = Piece(K533-2_repaired.mscx")
        >>> p[3] == p.measure[3]
        True

    Note that bs4 tags are just references to the ``soup`` object, but when printed,
    the nodes are shown::

        >>> p[46]
        {'number': '46',
         'start': 64800,
         'len': [1440],
         'timesig': '3/4',
         'keysig': '-2',
         'harmonies': {0: 'I(974)', 480: 'I\\\\'},
         'events': {0: {...}
                    480: {...}
                    960: {...}
                    },
         'node': [<Measure number="46">...</Measure>]}

    The integer values are ticks. 'start' designates the measure's offset.
    The keys of the 'harmonies' and 'events' (see below) dictionaries are offsets from 'start' value.
    Note that the 'len' (length) and the 'node' are given as lists because sometimes one
    measure can be split and represented by two measure tags in the MSCX document.::

        >>> p[46]['events']
        {0: { 'node': <Chord>...</Chord>,
              'type': 'Chord',
              'value': 'quarter',
              'duration': 480.0,
              'harmony': 'I(974)',
              'harmony_tag': <Harmony><name>I(974)</name></Harmony>,
              'voice': 0},
         480: {'node': <Chord>...</Chord>,
              'type': 'Chord',
              'value': 'quarter',
              'duration': 480.0,
              'harmony': 'I\\\\',
              'harmony_tag': <Harmony> <name>I\\</name></Harmony>,
              'voice': 0},
         960: {'node': <Rest><durationType>quarter</durationType></Rest>,
              'type': 'Rest',
              'value': 'quarter',
              'duration': 480.0,
              'harmony': '',
              'harmony_tag': '',
              'voice': 0}
        }

        >>> p[46]['harmonies']
        {0: 'I(974)', 480: 'I\\\\'}
    """
    def __init__(self,mscx,repair=False,ms="mscore",timesig_map_only=False):
        """Creates the data structure of the Piece() object

        Parameters
        ----------

        mscx: str
            Path to the MuseScore2 file to be parsed.
        repair: bool, optional
            The parser always performs autocorrect for consistent representation.
            Pass True to save corrected files with the suffix _repaired
        ms: str, optional
            Path to MuseScore executable. Pass "win" for standard path under Windows.
            Defaults to 'mscore' which is the command on UNIX systems.
        timesig_map_only: bool, optional
            If you need the object to hold only time signatures and key, not the harmonies, pass True
            This saves a lot of time.

        Example
        -------

        >>> p = Piece("K533-2.mscx",True)
        K533-2.mscx m. 23: Moved label I to upper system.
        K533-2.mscx m. 117: Moved label V43/IV to upper system.
        K533-2.mscx => K533-2_repaired.mscx
        All good.

        """

        if ms == "win":
            ms = "C:\\Program Files (x86)\\MuseScore 2\\bin\\MuseScore.exe"
        self.mscore = ms
        self.tsm_only = timesig_map_only
        self.measure = {}
        self.timesig = ''
        self.key = ''
        self.keysig = "0"
        self.irregular = False     # flag for checking the completenes of measures (split measures appear as individual tags, each with attribute 'len')
        self.substract = 0          # helps constructing correct measure numbers if incomplete measures exist
        self.len = 0                # length of the piece in ticks (quarter note = 480 ticks, whole note = 1920 ticks)
        self.tuplets = {}           # dict with id: tuplet fraction, e.g. {"1": Fraction(7/4)}
        self.volta_measures = []
        self.repair = repair
        self.corrections = False    # if True, will result in a dump() if repair == True
        self.has_harmonies = False
        self.source = mscx
        self.piece = os.path.basename(mscx)
        self.dir = os.path.dirname(mscx)
        with open(mscx, 'r') as file:
            ### Object representing the XML structure to be altered
            self.soup = BeautifulSoup(file.read(), 'xml')
        self.firststaff = self.soup.find('Part').find_next_sibling('Staff')
        self.otherstaves = self.firststaff.find_next_siblings('Staff')

        if self.tsm_only:
            frst = self.firststaff.find("Harmony").find("name").string.split('.')
            self.key = frst[0] if frst[0] != '' else frst[1]

        #save all tuplets
        for x in self.soup.find_all("Tuplet", id=True): # loop over all <Tuplet> tags
            if x.find('Tuplet'): # this is a nested tuplet, so the fraction has to be multiplied by that of the parent tuplet
                self.tuplets[x['id']] = Fraction(int(x.normalNotes.string), int(x.actualNotes.string)) * self.tuplets[x.find('Tuplet').string]
            else:
                self.tuplets[x['id']] = Fraction(int(x.normalNotes.string), int(x.actualNotes.string))

        measures = self.firststaff.find_all('Measure')
        if len(measures) == 0:
            print(self.piece + " includes no measures.")
            return
        #Deal with pickup measure (in that case the two first measures should have number "1")
        self.pickup = True if measures[1]['number'] == "1" else False
        if not self.pickup and measures[0].has_attr('len'):

            if self.repair:
                self.pickup = True
                print(f"{self.piece}: 1st measure has attribute len={measures[0]['len']}. Corrected its measure number from 1 to 0.")
                self.corrections = True
            else:
                print(f"{self.piece}: 1st measure has attribute len={measures[0]['len']} and might be a pickup measure with erroneous measure number 1. To correct, call Piece(\'{self.source}\',True).")


        for i,x in enumerate(measures):

            if x.find('TimeSig'):
                self.timesig = f"{x.find('sigN').string}/{x.find('sigD').string}"

            if x.find('KeySig'):
                try:
                    self.keysig = x.find('accidental').string
                except:
                    pass

            if self.pickup:
                if i == 0 and not x.find("irregular"):
                    tag = self.soup.new_tag("irregular")
                    x.append(tag)
            else:
                i += 1 # if there is no pickup, measure 1 is saved with index 1 instead of 0

            i -= self.substract
            skip = False
            if x.find('Volta'):
                number = x.find('Volta').find('text').string
                n = int(re.search(r'(\d*)',number)[0])
                if n == 1:
                    self.volta_measures.append(i)
                    self.measure[float(str(i)+".1")] = self.read_measure(str(i)+".1",x,self.len) #In case annotators use 8.1 or 8.2 for annotating voltas
                elif n > 1:
                    i -= 1
                    #self.len -= sum(self.measure[i]['len'])
                    offset = x.find("noOffset")
                    if offset:
                        self.substract -= int(offset.string) # value generally is negative
                    else:
                        self.substract += 1
                        offset = self.soup.new_tag("noOffset")
                        offset.string = "-1"
                        x.append(offset)
                    skip = True
                    self.measure[float(f"{i}.{n}")] = self.read_measure(f"{i}.{n}",x,self.len)

            goon = False
            if x.find('noOffset') and not skip and not x.has_attr('len'):
                val = -int(x.find('noOffset').string)
                self.substract += val
                i -= val
                self.add_to_measure(i,x)
                goon = True


            old = x['number']
            if old != str(i) and i > 0:
                if self.irregular:
                    if old != str(i+1):
                        self.change_number(x,i+1)
                else:
                    self.change_number(x,i)

            if goon:
                continue

            if x.has_attr('len') and i > 1:
                l = int(Fraction(x['len']) * 1920)
                timesig = int(Fraction(self.timesig) * 1920)
                if l != timesig:

                    prev = i-1
                    if not self.irregular: # if the previous bar was complete
                        self.irregular = True
                        self[i] = x # this calls self.__setitem__ which saves the measure in the measure dictionary
                    elif self.measure[prev]['len'][0] + l != timesig and not skip:
                            print(f"m. {prev} (len {sum(self.measure[prev]['len'])}) and m. {i} (len {l}) don't add up to {timesig}.")
                            self[i] = x
                    elif skip:
                        pass
                    else:
                        self.substract += 1
                        self.irregular = False
                        self.add_to_measure(prev,x)

                        if not x.find('irregular'):
                            tag = self.soup.new_tag("irregular")
                            x.append(tag)
                        if x.find("noOffset"):
                            x.find("noOffset").decompose()
                else:
                    self[i] = x
            elif self.irregular:
                if skip:
                    self.irregular = False
                else:
                    print(f"m. {i-1} is incomplete and m. {i} does not complete it. Correct manually using MuseScores \'Bar Properties\'")
                    self.irregular = False
                    self[i] = x
            else:
                self[i] = x # this calls self.__setitem__ which saves the measure in the measure dictionary



        for i,x in enumerate(self.soup.find_all('Harmony')):
            if not x.find('name').string:
                x.decompose()
                self.corrections = True
                if not self.repair:
                    print(f"""Empty harmony tag removed. Use Piece({self.source},True) to autorepair.""")
                else:
                    print(f"{self.piece}: Empty harmony tag permanently removed.")

        for i,x in enumerate(self.otherstaves):
            if len(x.find_all('Harmony')) > 0:
                self.corrections = True
                if self.repair:
                    self.copy_harmonies(x)
                else:
                    print(f"{self.piece} contains harmonies in Staff {i+2} with id={x['id']}. To correct, call Piece(\'{self.source}\',True).")


        allh = self.get_harmonies()
        if len(self.volta_measures) == 0:
            lh = len(allh)
        else:
            lh = len(self.get_harmonies(include_voltas=True))
        ls = len(self.soup.find_all('Harmony'))
        if lh > 0:
            frst = allh[0][2].split('.')
            if len(frst) < 3:
                print(self.piece + '\'s first symbol does not indicate the tonality correctly. Leading dot missing?')
            else:
                self.key = frst[1]

        if self.corrections and self.repair:
            m = re.search(r'(.*).mscx',self.piece)
            new = "%s_repaired.mscx" % m.group(1)
            old = "%s.mscx" % m.group(1)
            print(f"{old} => {new}")
            self.dump(os.path.join(self.dir,new))
            #os.rename(self.piece,old)
            if len(self.volta_measures) == 0:
                lh = len(self.get_harmonies())
            else:
                lh = len(self.get_harmonies(include_voltas=True))
            ls = len(self.soup.find_all('Harmony'))
            if lh != ls:
                print(f"""Captured only {lh} out of the {ls} harmonies in {self.piece}. Please check the score manually.
                The easiest way to do so is getting and copying all captured harmonies via Piece.get_harmonies() and inserting them into your text editor next to the score.
                Then, search the score for <Harmony>: Check which result number does not correspond to the line number in the copied harmony document.""")
            #else:
                #print(f'Captured all {ls} harmonies in {new}')
        elif not self.repair and not self.tsm_only:
            if lh != ls:
                print(f"""Captured only {lh} out of the {ls} harmonies in {self.piece}. Use -r to keep changes.""")
            else:
                print("All good.")

###################### End of __init__ ############################

    def add_to_measure(self,prev,x):
        """Add the second part of a split measure.

        Parameters
        ----------

        prev: int
            Number of the measure's first part (already in the ``measure`` dictionary)
        x: bs4.element.Tag
            Node that is to be added as second part
        """
        i = int(x['number'])
        addition = self.read_measure(i,x,self.len)
        l = int(Fraction(x['len']) * 1920) if x.has_attr('len') else int(Fraction(addition['timesig']) * 1920)
        self.len += l
        self.measure[prev]['len'].append(l)
        if not self.tsm_only:
            self.measure[prev]['node'].append(x)
            prev_l = self.measure[prev]['len'][0]
            for k, v in addition['events'].items():
                self.measure[prev]['events'][prev_l + k] = v
            for k, v in addition['harmonies'].items():
                self.measure[prev]['harmonies'][prev_l + k] = v


    def __getitem__(self, key):
        return self.measure[key]

    def __setitem__(self, key, knot):
        self.measure[key] = self.read_measure(key, knot,self.len)
        self.len += self.measure[key]['len'][0]

    def missing_dot(self,h,tag):
        """Corrects a harmony label if a necessary leading dot was forgotten.

        If a label starts with a note name, MuseScore2 saves the notename in a
        <root> tag and does not display it. This is corrected here.

        Parameters
        ----------

        h: string
            'broken' label without the leading note Name
        tag: bs4.element.Tag
            The node that has to be repaired
        """
        root = tag.find('root')
        if root:
            global tonal_pc
            if root.string in tonal_pc:
                letter = tonal_pc[root.string]
                new = f'.{letter}{h}'
                root.decompose()
                tag.find('name').string = new
                self.corrections = True
                return new
            else:
                return h + "!"
        else:
            return h

    def read_measure(self, key, knot, start):
        """Reads and stores the information from a <measure> node.

        Upon initializing, this function is called for each measure of the first staff.
        It returns a dictionary holding the information that is stored in the ``measure`` dictionary.

        Parameters
        ----------
        key: key
            Under which the result is going to be saved. Stereotypically an integer with the measure number.
            Voltas are stored as 8.1 or 8.2 etc.
        knot: bs4.element.Tag
            The <measure> node to be extracted from
        start: integer
            The measure's offset in ticks

        """
        events = {} # dictionary holding all the rests and chords in this measure
        sec_events = {}
        harmonies = {}
        pos = 0 #pointer in ticks, 0 is beat 1 of this measure

        try:
            length = int(Fraction(knot['len']) * 1920) #if measure has irregular length (e.g. pickup measure)
        except:
            length = int(Fraction(self.timesig) * 1920)

        if self.tsm_only:
            return {'len': [length], # in ticks
                    'timesig':self.timesig,
                    'harmonies':{}}
        else:


            def save_events(x,track,tick):
                """Turns a <Chord> or <Rest> tags into a dictionary.

                Each event's information which is necessary in this context is stored,
                including the reference to its tag, so it can be changed. The resulting
                dictionary is stored in the ``events`` dictionary which in turn lives in
                the ``measure`` dictionary.

                Parameters
                ----------

                x: bs4.element.Tag
                    The tag of the element in question
                track: integer
                    Information in which voice the event occurs with 0 being the main voice (blue in MuseScore2)
                tick:
                    Information about the event's offset from the measure's beginning.

                """
                value = x.find('durationType').string # note value in words such as "half" (--> conversion dictionary)
                prev = get_sibling(x.find('durationType'),False) # previous node, potentially indication <dots>
                sca = sum([0.5 ** i for i in range(int(prev.string)+1)]) if prev and prev.name == 'dots' else 1 # scalar depending on dots
                sca = sca * self.tuplets[x.find('Tuplet').string] if x.find('Tuplet') else sca # altering scalar if in a tuplet
                duration = durations[value] * 1920 * sca
                h = ''
                prev = get_sibling(x,False)
                while prev and prev.name in skip_tags + ['Chord']: #skip_tags contains Tags which can appear between Harmony and Chord
                    if prev.name == 'Chord':
                        if not prev.find(grace_tags):
                            break
                    elif prev.name == 'Harmony':
                        candidates = []
                        candidates.append(prev)
                        check = get_sibling(prev,False)
                        if check and check.name == 'Harmony':
                            candidates.append(check)
                        candidates = list(filter(lambda x: x.find('name').string != None,candidates))
                        labels = [x.find('name').string for x in candidates] #collect non-empty Harmony tags
                        l = len(labels)
                        if l == 1:
                            h = labels[0]
                            prev = candidates[0]
                        elif l == 2:
                            if labels[0] == labels[1]:
                                self.corrections = True
                                prev = candidates[1]
                                h = labels[1]
                                candidates[0].decompose()
                                if self.repair:
                                    print(f"{self.piece}: Removed identical harmony in m. {key} on tick {tick}.")
                                else:
                                    print(f"""{self.piece}: Two identical harmonies appear in m. {key} on tick {tick}, one has been temporally deleted.
                                            To keep this change, use Piece('{self.source}',repair=True).""")
                            else:
                                print(f"{self.piece}: Two different labels are assigned to m. {key}, tick {tick}: {labels[0]} and {labels[1]}. Please delete one.")
                        break #Harmony found, end of loop
                    prev = get_sibling(prev,False)
                if h == '':
                    prev = ''
                elif self.has_harmonies:
                    new = self.missing_dot(h,prev)
                    if not new == h:
                        if new[-1] == '!':
                            print(f"m. {key}, tick {tick}: {h} contains an error, probably because of a missing dot.")
                        elif self.repair:
                            print(f"m. {key}, tick {tick}: Corrected {h} to {new}.")
                            h = new
                        else:
                            print(f"m. {key}, tick {tick}: {h} Needs to be corrected to {new}. Use -r")
                            h = new
                else:
                    self.has_harmonies = True
                return {
                    'node': x, # needed to insert a harmony label
                    'type': x.name, # Rest or Chord? (not needed)
                    'value': value,
                    'duration': duration,
                    'harmony': h,
                    'harmony_tag':prev,
                    'voice':track
                    }
                ####################### END save_events ##########################

            pos = 0
            for i, n in enumerate(knot.find_all(['Rest','Chord'])):
                if not n.find('acciaccatura'):
                    if n.find("track"):     #events in secondary voices to be treated later
                        track = int(n.find("track").string)
                        if not track in sec_events:
                            sec_events[track] = []
                        sec_events[track].append(n)
                    elif not n.find(grace_tags):
                        event = save_events(n,0,pos)

                        if event['harmony'] != '':
                            harmonies[pos] = event['harmony']
                            events[pos] = event
                        elif not n.find('visible'): # invisible events get only saved if they bear a harmony --> as a precaution, no new harmonies should be attached to invisible events
                            events[pos] = event
                        pos += event['duration']
                        if abs(pos-round(pos)) <= 0.01:
                            pos = round(pos)

            for k,v in sec_events.items(): #now add events from secondary voices if they don't occur synchronously
                pos = 0
                #orig_pos = 0
                for e in v: # for every event in every secondary voice
                    #orig_pos = pos

                    pot_tick = get_sibling(e,False)
                    while pot_tick and pot_tick.name in skip_tags + ['tick']:
                        if pot_tick.name == 'tick':
                            pos = int(pot_tick.string)-start
                            break
                        pot_tick = get_sibling(pot_tick,False)
                    event = save_events(e,k,pos)
                    if not pos in events and not e.find('visible'):
                        events[pos] = event
                    if event['harmony'] != '':
                        if not pos in harmonies:
                            harmonies[pos] = event['harmony']
                        elif harmonies[pos] == event['harmony']:
                            event['harmony_tag'].decompose()
                            self.corrections = True
                            if self.repair:
                                print(f"{self.piece}: Removed identical harmony in m. {key} on tick {str(pos)} in voice {track +1}.")
                        else:
                            print(f"{self.piece} m. {str(key)} tick {str(pos)}: voice {track +1} tries to override {harmonies[pos]} with {event['harmony']}. Repair manually.")
                    #pos = orig_pos
                    pos += event['duration']
                    if abs(pos-round(pos)) <= 0.01:
                        pos = round(pos)

            for i, n in enumerate(knot.find_all('tick')):
                orig_tick = int(n.string)
                tick = orig_tick-start
                n1 = get_sibling(n)
                if tick < 0:
                    # if self.repair:
                    #     self.corrections = True
                    #     n.string = str(orig_tick - tick)
                    #     print(f"Shifted tick {orig_tick} in m. {key} by {-tick}, i.e., to the beginning of the measure.")
                    #     tick = 0
                    # else:
                    print(f"m. {key}: The tick before the {n1.name}-Tag is at tick {tick} relative to the measure's beginning. Autorepair would move it to 0.")
                elif tick > length:
                    print(f"m. {key}: The tick before the {n1.name}-Tag occurs at tick {tick-length} after the measure. Autorepair not implemented.")
                if n1 and n1.name == 'Harmony':
                    h = n1.find('name').string
                    if not h:
                        n1.decompose()
                        self.corrections = True
                        if not self.repair:
                            print(f"""Empty harmony tag removed in m. {key} on tick {tick}.
                                    Dump() to new file to keep the change or use Piece(file,repair=True).""")
                        else:
                            print(f"{self.piece}: Empty harmony tag permanently removed in m. {key} on tick {tick}.")
                        continue
                    n2 = get_sibling(n1)
                    n2 = n2.name if n2 else 'endOfMeasure'
                    if not n2 in ['Chord','Rest']:
                        if not tick in harmonies:
                            if self.has_harmonies:
                                new = self.missing_dot(h,n1)
                                if not new == h:
                                    if new[-1] == '!':
                                        print(f"m. {key}, tick {tick}: {h} contains an error, probably because of a missing dot.")
                                    elif self.repair:
                                        print(f"m. {key}, tick {tick}: Corrected {h} to {new}.")
                                        h = new
                                    else:
                                        print(f"m. {key}, tick {tick}: {h} Needs to be corrected to {new}. Use -r")
                                        h = new
                            else:
                                self.has_harmonies = True
                            harmonies[tick] = h
                        #else:
                        #    print(f"Error in score: Two harmonies set in measure {str(key)}: Trying to capture {h} at tick {str(tick)}!")

            last_tag = knot.contents[-1]
            if isinstance(last_tag, NavigableString):
                last_tag = get_sibling(last_tag,False)
            if last_tag:
                if last_tag.name == 'Harmony' and not get_sibling(last_tag,False).name =='tick':
                    print(f"{self.piece} m. {key}: The <Harmony> tag containing \'{last_tag.find('name').string}\' is not properly attached to an event. Please correct manually.")
                #else:
                    #print(last_tag.name,get_sibling(last_tag,False).name)


            return { # now the measure information is ready to be stored
            'number': knot['number'],
            'start': start, # measure's onset in ticks
            'len': [length], # in ticks
            'timesig':self.timesig,
            'keysig':self.keysig,
            'harmonies': {key: harmonies[key] for key in sorted(harmonies.keys())},
            'events': {key: events[key] for key in sorted(events.keys())},
            'node': [knot], # harmonies are inserted here
            }
        ####################### END read_measure ##########################


    def change_number(self, node, n):
        """Changes the number of a measure in the <measure> nodes of all staves.

        Parameters
        ----------

        node: bs4.element.Tag
            <measure> node to be altered
        n: int
            New measure number

        """
        old_n = node['number']
        node['number'] = str(n)
        if self.repair:
            self.corrections = True
            print(f"Correct {old_n} to {n}")
            for j,y in enumerate(self.otherstaves):
                m = y.find_all("Measure", number=old_n)
                if len(m) > 1:
                    print("Correction of numbers which exist more than once within the same voice has not been implemented yet.")
                elif len(m) == 1:
                    m[0]['number'] = n
        else:
            print(f"measure number {old_n} should be corrected to {n}")


    def add_harmony(self, m, b, h,tic=False): # adds the harmony label h at beat b (quarter beats) of measure m
        """Inserts a harmony label at the given position.

        Parameters
        ----------

        m: int
            Measure number
        b: number
            Beat number. Will be converted into ticks. If you are passing beats
            in ticks already, set tic=True
        h: str
            Harmony label to be inserted
        tic: bool, optional
            Pass True if you pass a tick value for the beat (offset from measure's beginning)

        """
        beat = int((b - 1) * 480) if not tic else b
        tick = self.measure[m]['start'] + beat # measure's offset
        if m == 0:
            beat = beat - (int(Fraction(self.timesig) * 1920) - self.measure[m]['len'][0])
        if not beat in self.measure[m]['harmonies'].keys():
            self.measure[m]['harmonies'][beat] = h
            ### create the new <Harmony><name>h</name></Harmony> structure
            h_tag = self.soup.new_tag("Harmony")
            h_name = self.soup.new_tag("name")
            h_name.string = h
            h_tag.append(h_name)
            newline = NavigableString('\n')

            if not beat in self.measure[m]['events']:   # if at this beat there is no event to attach the harmony to:
                ends = [self.measure[m]['start'] + l for l in self.measure[m]['len']]
                if tick > ends[-1]:
                    return f"Trying to place {h} at tick {tick} in m. {m} which ends at tick {ends[-1]}."
                i = 0
                while tick > ends[i]:
                    i += 1
                node = self.measure[m]['node'][i]
                t_tag = self.soup.new_tag("tick")       #create additional <tick>offset</tick> tag
                t_tag.string = str(tick)
                node.append(h_tag)
                h_tag.insert_before(t_tag)
                h_tag.insert_before(newline)
            else: #if at this beat an event occures, attach the harmony to it
                if self.measure[m]['events'][beat]['voice'] > 0:
                    h_track = self.soup.new_tag("track")
                    h_track.string = str(self.measure[m]['events'][beat]['voice'])
                    h_tag.append(h_track)
                self.measure[m]['events'][beat]['node'].insert_before(h_tag)
                h_tag.insert_after(newline)
            return tick, h
        else:
            print(f"{self.piece}: In tick {beat} of m. {m} already holds label {self.measure[m]['harmonies'][beat]} !")


    def copy_harmonies(self,from_staff):
        """Move harmonies from lower staves to the upper staff.

        Parameters
        ----------

        from_staff: bs4.element.Tag
            The staff node from which all harmonies are moved
        """
        for i,x in enumerate(from_staff.find_all("Measure")):
            labels = x.find_all("Harmony")
            if len(labels) > 0:
                n = int(x['number'])
                m = self.read_measure(n,x,self.measure[n]['start'])
                for tick, harmony in m['harmonies'].items():
                    self.add_harmony(n,tick,harmony,True)
                    print(f"{self.piece} m. {n}: Moved label {harmony} to upper system.")
                for j,y in enumerate(labels): #delete tags
                    y.decompose()

    def add_space(self, s):
        """Adds space between harmony labels and the upper system.

        Parameters
        ----------

        s: number
            Good values lie between 4-7. The unit is sp
        """
        space = self.soup.new_tag("harmonyY")
        space.string = str(s)
        self.soup.find("Style").insert(0, space)


    def dump(self,filename):
        """Saves the altered XML structure as *filename*

        """
        ### the following code makes sure that <opening>and</closing> are written into the same line
        unformatted_tag_list = []
        for i, tag in enumerate(self.soup.find_all()):
            unformatted_tag_list.append(str(tag))
            tag.replace_with('{' + 'unformatted_tag_list[{0}]'.format(i) + '}')
        pretty_markup = self.soup.prettify().format(unformatted_tag_list=unformatted_tag_list) #writes tags into the same line

        with open(filename, "w") as file:
            file.write(pretty_markup)
        ######################################
        #Convert with MuseScore
        subprocess.run([self.mscore,"-o",filename,filename], encoding='utf-8', stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self = self.__init__(filename)
        return pretty_markup

    def get_harmonies(self,only_wrong=False,b='beats',keys=False,include_voltas=False):
        """Returns a list of lists with all harmonies and their positions.

        Parameters
        ----------

        only_wrong: bool, optional
            Set True if you are checking for syntactic errors in the labels.
        b: {'beat','tick'}, optional
            Pass 'tick' if your passing ticks as beats
        keys: bool, optional
            Extend the harmonies' lists by their local key and applied key.
        include_voltas: bool, optional
            If the default False is set, only the second volta's harmonies are given to avoid doubling.

        Examples
        --------

            >>> p.get_harmonies()
            [[1, '1', '.Bb.I'],
             [1, '2', 'viio6'],
             [1, '3', 'I6'],
             [2, '1', 'viio65/V'],
                    ...
             [121, '1', 'I'],
             [121, '3', 'V7'],
             [122, '1', 'I(974)'],
             [122, '2', 'I\\\\']]

            >>> p.get_harmonies(keys=True)
            [[0, '1', '.F.I', 'I', ''],
             [1, '3', 'viio', 'I', ''],
             [2, '1', 'I', 'I', ''],
             [3, '3', 'viio', 'I', ''],
                        ...
             [83, '1', 'V(64)', 'V', ''],
             [84, '1', 'vii%7', 'II', 'V'],
             [85, '1', 'V(64)', 'V', ''],
                        ...
             [90, '4', 'iii6', 'V', ''],
             [91, '1', '#viio65', 'vi', 'ii']]

         The last element of each list is only set if the label is an applied chord and shows the key
         that the label is applied to (in the example ``V`` and ``ii``). To learn the actual key of this
         applied chord, though, it has to be interpreted within the local key that it appears in, which is
         in both cases ``V``. Therefore the absolute keys which appear as fourth element of each list are
         ``II`` and ``vi``.

        """
        harmonies = []
        for m, measure in self.measure.items():
            if not float(m).is_integer() and not include_voltas:
                continue
            for tick, harmony in measure['harmonies'].items():
                if b == 'ticks':
                    beat = int(tick) if type(tick) == float and tick.is_integer() else tick
                elif b == 'beats':
                    beat = str(tick // 480 +1)
                    if tick % 480 > 0:
                        subbeat = Fraction((tick % 480)/480).limit_denominator(128)
                        beat = str(beat) + '.' + str(subbeat)

                if only_wrong:
                    alternatives = harmony.split('-')
                    for h in alternatives:
                        if not re.match(regex,h):
                            harmonies.append([m, beat, harmony])
                else:
                    harmonies.append([m, beat, harmony])

        if len(harmonies) == 0:
            return []
        elif include_voltas:
            for i in reversed(range(0,len(harmonies))):
                if harmonies[i][0] in self.volta_measures:
                    del harmonies[i]

        if keys:
            if self.key[0].isupper():
                one = 'I'
                minor = False
            else:
                one = 'i'
                minor = True
            locl = one
            for i,l in enumerate(harmonies):
                h = l[2]
                if i > 0 and h.find('.',1) != -1:
                    if h[0] == '.':
                        h = h[1:]
                    spl = h.split('.')
                    locl = spl[0]
                    h = ''.join(spl[1:])

                if h.find('/') != -1:
                    spl = h.split('/')
                    applied = re.match(r"(b*|\#*)(VII|VI|V|IV|III|II|I|vii|vi|v|iv|iii|ii|i)",spl[1]).group(0)
                    l.append(appl(applied,locl,minor))
                    h = h.replace('/'+spl[1],'')
                    appli = applied
                else:
                    l.append(locl)
                    appli = ''
                l.append(appli)
                l[2] = h

        return sorted(harmonies, key=lambda x: (x[0], beat2float(x[1])))

    def get_timesig_map(self):
        """Returns a dictionary with all measure numbers and their associated time signatures.

        """
        return {m: measure['timesig'] for m, measure in self.measure.items()}


    def remove_harmonies(self,target):
        """Removes all harmony labels from the score and saves it to *target*

        Parameters
        ----------

        target: str
            Path to the newly written file without harmonies

        """
        for i, tag in enumerate(self.soup.find_all("Harmony")):
            prev = get_sibling(tag, False)
            if prev:
                if prev.name == 'tick':
                    prev.decompose()
            tag.decompose()
        self.dump(target)
        print(target+" written.")

    def get(self,first,last=None,dir=None,extension="png",dpi=None):
        """Show an extract from a score and save it to a file.

        Parameters
        ----------

        first: int
            first measure of the extract
        last: int, optional
            last measure of the extract, can be -1
        dir: str, optional
            Directory where the file(s) will be saved
        extension: {'png','svg','pdf','mscz','mscx','wav','mp3','flac','ogg','xml','mxl','mid'}, optional
            Decides what format the excerpt is saved as by MuseScore2. If not an image, set show=False
        dpi: int, optional
            In the case of saving a png image, you can set the resolution. Otherwise, MuseScore uses the
            standard value set in the configuration.
        """
        if dir is None:
            dir = self.dir
        if not os.path.isdir(dir):
            if input(dir + " does not exist. Create or use MSCX file's location. Create? (y|n)") == "y":
                os.mkdir(dir)
            else:
                dir = self.dir
                print("dir set to " + self.dir)
        measures_right = []
        measures_left = []
        if first == -1:
            first = max(self.measure.keys())
        if last == -1:
            last = max(self.measure.keys())
        elif last is None:
            last = first
        measure_list = sorted([m for m in self.measure.keys() if first <= m <= last]) # wird bei Voltas Probleme machen
        try:
            start_tick = self.measure[measure_list[0]]['start']
        except:
            print("No such measure")
        for m in measure_list:
            nodes = self.measure[m]['node']

            for n in nodes:
                num = n['number']
                if n.has_attr('len'):
                    l = n['len']
                    left = copy(self.otherstaves[0].find(number=num,len=l))
                else:
                    left = copy(self.otherstaves[0].find(lambda x: x.has_attr('number') and x['number']==num and not x.has_attr('len')))
                for measure in [n,left]:
                    for i,t in enumerate(measure.find_all('tick')):
                        tick = int(t.string)
                        t.string = str(tick-start_tick)
                measures_left.append(left)
                measures_right.append(copy(n))
        if not measures_right[0].find('TimeSig'):
            ############################################################
            # this block could be replaced by
            # t_tag = self.firststaff.find('TimeSig')
            # but then the excerpt would get the time signature from the beginning
            ############################################################
            timesig=self.measure[measure_list[0]]['timesig'].split('/')
            tmp = BeautifulSoup('','xml')
            t_tag = tmp.new_tag('TimeSig')
            n_tag = tmp.new_tag('sigN')
            d_tag = tmp.new_tag('sigD')
            s_tag = tmp.new_tag('showCourtesySig')
            n_tag.string = timesig[0]
            d_tag.string = timesig[1]
            s_tag.string = "1"
            for t in [n_tag,d_tag,s_tag]:
                t_tag.append(t)
            ############################################################
            measures_right[0].insert(0,copy(t_tag))
            measures_left[0].insert(0,copy(t_tag))
        if not measures_right[0].find('KeySig'):
            keysig=self.measure[measure_list[0]]['keysig']
            if keysig != "0":
                tmp = BeautifulSoup('','xml')
                k_tag = tmp.new_tag('KeySig')
                a_tag = tmp.new_tag('accidental')
                a_tag.string = keysig
                k_tag.append(a_tag)
                measures_right[0].insert(0,copy(k_tag))
                measures_left[0].insert(0,copy(k_tag))
        grid = BeautifulSoup(empty, 'xml')
        right = grid.find('Part').find_next_sibling('Staff')
        left = right.find_next_sibling('Staff')
        for r in measures_right:
            right.append(r)
        for l in measures_left:
            left.append(copy(l))
        if first > 1:
            offset_tag = grid.new_tag('noOffset')
            offset_tag.string = str(first-1)
            right.find('Measure').insert(0,offset_tag)

        name=f"{self.piece.replace('.mscx','')}m{first}-{last}"
        png=os.path.join(dir,name+'.'+extension)
        fp = tempfile.NamedTemporaryFile(mode='w',encoding='utf-8',suffix='.mscx', delete=False)
        fp.write(str(grid))
        fp.close()
        command = [self.mscore,"-o",png,fp.name,"-T","0"]
        if dpi:
            command.extend(["-r",str(dpi)])
        subprocess.run(command,stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        #subprocess.run([self.mscore,fp.name]) #show tmp file
        os.remove(fp.name)
        createdfiles = sorted(list(filter(lambda x: re.match(name+'.*\.'+extension,x),os.listdir(dir))))
        try:
            display(Image(filename=os.path.join(dir,createdfiles[0])))
        except:
            print(f"created {createdfiles} in {dir}")
########################################### End of Class Piece
