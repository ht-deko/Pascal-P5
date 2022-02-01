﻿{*******************************************************************************
*                                                                              *
*                     Portable Pascal assembler/interpreter                    *
*                     *************************************                    *
*                                                                              *
*                                 Pascal P5                                    *
*                                                                              *
*                                 ETH May 76                                   *
*                                                                              *
* Authors:                                                                     *
*    Urs Ammann                                                                *
*    Kesav Nori                                                                *
*    Christian Jacobi                                                          *
*    K. Jensen                                                                 *
*    N. Wirth                                                                  *
*                                                                              *
*    Address:                                                                  *
*       Institut Fuer Informatik                                               *
*       Eidg. Technische Hochschule                                            *
*       CH-8096 Zuerich                                                        *
*                                                                              *
*  This code is fully documented in the book                                   *
*        "Pascal Implementation"                                               *
*   by Steven Pemberton and Martin Daniels                                     *
* published by Ellis Horwood, Chichester, UK                                   *
*         ISBN: 0-13-653-0311                                                  *
*       (also available in Japanese)                                           *
*                                                                              *
* Steven Pemberton, CWI/AA,                                                    *
* Kruislaan 413, 1098 SJ Amsterdam, NL                                         *
* Steven.Pemberton@cwi.nl                                                      *
*                                                                              *
* Adaption from P4 to P5 by:                                                   *
*                                                                              *
*    Scott A. Moore                                                            *
*    samiam@moorecad.com                                                       *
*                                                                              *
*    The comments marked with brackets are mine [sam]                          *
*                                                                              *
* Note that the previous version of P4 added some type specified instructions  *
* that used to be unified, typeless instructions.                              *
*                                                                              *
* P5 errors added:                                                             *
*                                                                              *
* 182 identifier too long                                                      *
* 183 For index variable must be local to this block                           *
* 184 Interprocedure goto does not reference outter block of destination       *
* 185 Goto references deeper nested statement                                  *
* 186 Label referenced by goto at lesser statement level                       *
* 187 Goto references label in different nested statement                      *
* 188 Label referenced by goto in different nested statement                   *
* 189 Parameter lists of formal and actual parameters not congruous.           *
*                                                                              *
* P5 instructions modified:                                                    *
*                                                                              *
* lca'string'       '                                                          *
*                                                                              *
* was changed to                                                               *
*                                                                              *
* lca 'string'''                                                               *
*                                                                              *
* That is, lca has a space before the opening quote, no longer pads to the     *
* right, and represents single quotes with a quote image. pint converts quote  *
* images back to single quotes, and pads out strings to their full length.     *
*                                                                              *
* In addition, the way files work was extensively modified. Original P5 could  *
* not represent files as full1y expressed variables, such as within an array   *
* or record, and were effectively treated as constants. To treat them as True  *
* variable accesses, the stacking order of the file in all file subroutines    *
* was changed so that the file is on the bottom. This matches the source       *
* order of the file in Write(f, ...) or Read(f, ...). Also, the file           *
* operations now leave the file on the stack for the duration of a Write or    *
* Read, then dump them using a specific New instruction "dmp". This allows     *
* multiparameter writes and reads to be effectively a chain of single          *
* operations using one file reference. Finally, files were tied to the type    *
* ending 'a', because files are now full variable references.                  *
*                                                                              *
*******************************************************************************}

program pascalcompiler(Output, prd, prr);
{$APPTYPE Console}
{$WEAKLINKRTTI ON}
{$RTTI EXPLICIT METHODS([]) PROPERTIES([]) FIELDS([])}

uses
  System.SysUtils, System.Math, System.IOUtils;

const

  { ************************************************************************

  Program object sizes and characteristics, sync with pint. These define
  the machine specific characteristics of the target.

  The configurations are as follows:

  type                  #bits 32  #bits 64
  ===========================================================
  integer               32        64
  real                  64        64
  char                  8         8
  boolean               8         8
  set                   256       256
  pointers              32        64
  marks                 32        64
  File logical number   8         8

  Both endian types are supported. There is no alignment needed, but you
  may wish to use alignment to tune the runtime speed.

  The machine characteristics dependent on byte accessable machines. This
  table is all you should need to adapt to any byte addressable machine.

  }

  { type               #32 #64 }
  intsize     =        4   {8};  { size of integer }
  intal       =        4;        { alignment of integer }
  intdig      =        11  {20}; { number of decimal digits in integer }
  inthex      =        8   {16}; { number of hex digits of integer }
  realsize    =        8;        { size of real }
  realal      =        4;        { alignment of real }
  charsize    =        1;        { size of char }
  charal      =        1;        { alignment of char }
  charmax     =        1;
  boolsize    =        1;        { size of boolean }
  boolal      =        1;        { alignment of boolean }
  ptrsize     =        4   {8};  { size of pointer }
  adrsize     =        4   {8};  { size of address }
  adral       =        4;        { alignment of address }
  setsize     =       32;        { size of set }
  setal       =        1;        { alignment of set }
  filesize    =        1;        { required runtime space for file (lfn) }
  fileidsize  =        1;        { size of the lfn only }
  stackal     =        4;        { alignment of stack }
  stackelsize =        4   {8};  { stack element size }
  maxsize     =       32;        { this is the largest type that can be on
                                   the stack }
  { Heap alignment should be either the natural word alignment of the
    machine, or the largest object needing alignment that will be allocated.
    It can also be used to enforce minimum block allocation policy. }
  heapal      =        4;        { alignment for each heap arena }
  gbsal       =        4;        { globals area alignment }
  sethigh     =      255;        { Sets are 256 values }
  setlow      =        0;
  ordmaxchar  =      255;        { Characters are 8 bit ISO/IEC 8859-1 }
  ordminchar  =        0;
  maxresult   = realsize;        { maximum size of function result }
  marksize    =       32   {56}; { maxresult+6*ptrsize }
  { Value of nil is 1 because this allows checks for pointers that were
    initialized, which would be zero (since we clear all space to zero).
    In the new unified code/data space scheme, 0 and 1 are always invalid
    addresses, since the startup code is at least that long. }
  nilval      =        1;  { value of 'nil' }

  { beginning of code, offset by program preamble:

    2:    mst
    6/10: cup
    1:    stp

  }
  begincode   =        9   {13};

  { Mark element offsets

    Mark format is:

    -8:  Function return value, 64 bits, enables a full real result.
    -12:  Static link.
    -16: Dynamic link.
    -20: Saved EP from previous frame.
    -24: Stack bottom after locals allocate. Used for interprocdural gotos.
    -28: EP from current frame. Used for interprocedural gotos.
    -32: Return address

  }
  markfv      =        -8   {0};  { function value }
  marksl      =        -12  {8};  { static link }
  markdl      =        -16  {16}; { dynamic link }
  markep      =        -20  {24}; { (old) maximum frame size }
  marksb      =        -24  {32}; { stack bottom }
  market      =        -28  {40}; { current ep }
  markra      =        -32  {48}; { return address }

  { ******************* end of pcom and pint common parameters *********** }

  displimit   = 300;
  maxlevel    = 255;
  { strglgth used to define the size of all strings in pcom and pint. With the
   string quanta system, string lengths are effectively unlimited, but there
   it still sets the size of some buffers in pcom. }
  strglgth    = 250;
  { maximum number of digits in real, including sign and exponent }
  digmax      = 250;
  { lcaftermarkstack is a very pcom specific way of stating the size of a mark
   in pint. However, it is used frequently in Perberton's documentation, so I
   left it, but equated it to the more portable marksize. }
  lcaftermarkstack = -marksize;
  fileal      = charal;
  {  stackelsize = minimum size for 1 stackelement
                = k*stackal
    stackal     = scm(all other al-constants)
    charmax     = scm(charsize,charal)
                  scm = smallest common multiple
    lcaftermarkstack >= maxresult+3*ptrsize+max(x-size)
                      = k1*stackelsize           }
  parmal     = stackal;
  parmsize   = stackelsize;
  recal      = stackal;
  maxaddr    =  maxint;
  maxsp      = 48;  { number of standard procedures/functions }
  maxins     = 82;  { maximum number of instructions }
  maxids     = 250; { maximum characters in id string (basically, a full line) }
  maxstd     = 39;  { number of standard identifiers }
  maxres     = 35;  { number of reserved words }
  reslen     = 9;   { maximum length of reserved words }
  varsqt     = strglgth; { variable string quanta }
  prtlln     = 10;  { number of label characters to print in dumps }

  { default field sizes for write }
  intdeff    = 11; { default field length for integer }
  reldeff    = 22; { default field length for real }
  chrdeff    = 1;  { default field length for char (usually 1) }
  boldeff    = 5;  { default field length for boolean (usually 5 for 'false' }

  { debug flags }

  dodmplex   = False; { dump lexical }
  doprtryc   = False; { dump recycling tracker counts }
  doprtlab   = False; { print labels }
  dodmpdsp   = False; { dump the display }

  { version numbers }

  majorver   = 1; { major version number }
  minorver   = 3; { minor version number }
  experiment = False; { is version experimental? }

  ERROR_HEADER = '*** Error: Compiler internal error';

type
                                                            { describing: }
                                                            { *********** }

  {marktype= ^Integer;}

                                                            { basic symbols }
                                                            { ************* }

  symbol = (ident, intconst, realconst, stringconst, notsy, mulop, addop, relop,
    lparent, rparent, lbrack, rbrack, comma, semicolon, period, arrow,
    colon, becomes, range, labelsy, constsy, typesy, varsy, funcsy, progsy,
    procsy, setsy, packedsy, arraysy, recordsy, filesy, beginsy, ifsy,
    casesy, repeatsy, whilesy, forsy, withsy, gotosy, endsy, elsesy, untilsy,
    ofsy, dosy, tosy, downtosy, thensy, nilsy, othersy);
  operator = (mul, rdiv, andop, idiv, imod, plus, minus, orop, ltop, leop, geop,
    gtop, neop, eqop, inop, noop);
  setofsys = set of symbol;
  chtp = (letter, number, special, illegal,
    chstrquo, chcolon, chperiod, chlt, chgt, chlparen, chspace, chlcmt);
  { Here is the variable length string containment to save on space. strings
    strings are only stored in their length rounded to the nearest 10th. }
  strvsp = ^strvs; { pointer to variable length id string }
  strvs = record { id string variable length }
            str: packed array[1..varsqt] of Char; { data contained }
            next: strvsp { next }
          end;

                                                            { constants }
                                                            { ********* }
  setty = set of setlow..sethigh;
  cstclass = (reel, pset, strg);
  csp = ^constant;
  constant = record
               next: csp; { next entry link }
               case cclass: cstclass of
                 reel: (rval: strvsp);
                 pset: (pval: setty);
                 strg: (slgth: 0..strglgth;
                        sval: strvsp)
             end;

  valu = record
           case {intval:} Boolean of { intval never set nor tested }
             True: (ival: Integer);
             False: (valp: csp)
         end;

                                                            { data structures }
                                                            { *************** }
  levrange = 0..maxlevel;
  addrrange = -maxaddr..maxaddr;
  stkoff = -maxaddr..0;
  structform = (scalar, subrange, pointer, power, arrays, records, files,
    tagfld, variant);
  declkind = (standard, declared);
  stp = ^structure;
  ctp = ^identifier;

  structure = record
                next: stp; { next entry link }
                marked: Boolean; { for test phase only }
                size: addrrange;
                packing: Boolean; { packing status }
                case form: structform of
                  scalar: (case scalkind: declkind of
                             declared: (fconst: ctp);
                             standard: ());
                  subrange: (rangetype: stp;
                             min, max: valu);
                  pointer: (eltype: stp);
                  power: (elset: stp;
                          matchpack: Boolean);
                  arrays: (aeltype, inxtype: stp);
                  records: (fstfld: ctp;
                            recvar: stp;
                            recyc: stp);
                  files: (filtype: stp);
                  tagfld: (tagfieldp: ctp;
                           fstvar: stp);
                  variant: (nxtvar, subvar, caslst: stp;
                            varval: valu)
              end;

                                                            { names }
                                                            { ***** }

  idclass = (types, konst, vars, field, proc, func);
  setofids = set of idclass;
  idkind = (actual, formal);
  idstr = packed array[1..maxids] of Char;
  restr = packed array[1..reslen] of Char;
  nmstr = packed array[1..digmax] of Char;
  csstr = packed array[1..strglgth] of Char;
  identifier = record
                 name: strvsp;
                 llink, rlink: ctp;
                 idtype: stp;
                 next: ctp;
                 keep: Boolean;
                 refer: Boolean;
                 case klass: idclass of
                   types: ();
                   konst: (values: valu);
                   vars: (vkind: idkind;
                          vlev: levrange;
                          vaddr: addrrange;
                          threat: Boolean;
                          forcnt: Integer);
                   field: (fldaddr: addrrange;
                           varnt: stp;
                           varlb: ctp;
                           tagfield: Boolean;
                           taglvl: Integer;
                           varsaddr: addrrange;
                           varssize: addrrange);
                   proc,
                   func: (pfaddr: addrrange;
                          pflist: ctp; { param list }
                          asgn: Boolean; { assigned }
                          case pfdeckind: declkind of
                            standard: (key: 1..18);
                            declared: (pflev: levrange;
                                       pfname: Integer;
                                       case pfkind: idkind of
                                         actual: (forwdecl,
                                                  externl: Boolean);
                                         formal: ()))
               end;

  disprange = 0..displimit;
  where = (blck, crec, vrec, rec);

                                                            { expressions }
                                                            { *********** }
  attrkind = (cst, varbl, expr);
  vaccess = (drct, indrct, inxd);

  attr = record
           typtr: stp;
           case kind: attrkind of
             cst: (cval: valu);
             varbl: (packing: Boolean;
                     packcom: Boolean;
                     tagfield: Boolean;
                     taglvl: Integer;
                     varnt: stp;
                     ptrref: Boolean;
                     vartagoff: addrrange;
                     varssize: addrrange;
                     case access: vaccess of
                       drct: (vlevel: levrange;
                              dplmt: addrrange);
                       indrct: (idplmt: addrrange);
                       inxd: ());
             expr: ()
         end;

                                                            { labels }
                                                            { ****** }
  lbp = ^labl;
  labl = record { 'goto' label }
           nextlab: lbp;     { next list link }
           defined: Boolean; { label defining point was seen }
           labval,           { numeric value of label }
           labname: Integer; { internal sequental name of label }
           vlevel: levrange; { procedure level of definition }
           slevel: Integer;  { statement level of definition }
           ipcref: Boolean;  { was referenced by another proc/func }
           minlvl: Integer;  { minimum goto reference statement lvl }
           bact: Boolean;    { containing block is active }
           refer: Boolean    { was referred to }
         end;

  { external file tracking entries }
  extfilep = ^filerec;
  filerec = record
              filename: idstr;
              nextfile: extfilep
            end;

  { case statement tracking entries }
  cip = ^caseinfo;
  caseinfo = record
               next: cip;
               csstart: Integer;
               cslab: Integer
             end;

  { Subrange Char }
  subchar = Chr(ordminchar)..Chr(ordmaxchar);

  { ------------------------------------------------------------------------- }

var

  prd, prr: text;  { Output code file }

                                  { returned by source program scanner
                                   insymbol:
                                   ********* }

  sy: symbol;                     { last symbol }
  op: operator;                   { classification of last symbol }
  val: valu;                      { value of last constant }
  lgth: Integer;                  { length of last string constant }
  id: idstr;                      { last identifier (possibly truncated) }
  kk: 1..maxids;                  { nr of chars in last identifier }
  ch: Char;                       { last character }
  eol: Boolean;                   { end of line flag }

                                  { counters: }
                                  { ********* }

  chcnt: Integer;                 { character counter }
  ic, gc: addrrange;              { data location and instruction counter }
  lc: stkoff;
  linecount: Integer;

                                  { switches: }
                                  { ********* }

  dp,                             { declaration part }
  list, prcode, prtables,
    chkvar: Boolean;              { Output options for
                                    -- source program listing
                                    -- printing symbolic code
                                    -- displaying ident and struct tables
                                    -- procedure option }
  debug: Boolean;                 { -- Debug checks }
  chkref: Boolean;                { -- Reference checks }
  chkudtc, chkudtf: Boolean;      { -- Check undefined tagfields, candidate
                                       and final }
  option: array['a'..'z'] of      { option array }
  Boolean;

                                  { pointers: }
                                  { ********* }
  parmptr,
    intptr, realptr, charptr,
    boolptr, nilptr, textptr: stp;{ pointers to entries of standard ids }
  utypptr, ucstptr, uvarptr,
    ufldptr, uprcptr, ufctptr,    { pointers to entries for undeclared ids }
  fwptr: ctp;                     { head of chain of forw decl type ids }
  outputptr, inputptr: ctp;       { pointers to default files }
  usclrptr: ctp;                  { used to satisfy broken record tag fields }
  fextfilep: extfilep;            { head of chain of external files }

                                  { bookkeeping of declaration levels: }
                                  { ********************************** }

  level: levrange;                { current static level }
  disx,                           { level of last id searched by searchid }
  top: disprange;                 { top of display }

  display:                        { where:   means: }
  array[disprange] of
    packed record                 { =blck:   id is variable id }
      fname: ctp;
      flabel: lbp;                { =crec:   id is field id in record with }
      fconst: csp;
      fstruct: stp;
      packing: Boolean;           { used for with derived from packed }
      packcom: Boolean;           { used for with derived from packed }
      ptrref: Boolean;            { used for with derived from pointer }
      case occur: where of        {    constant address }
        crec: (clev: levrange;    { =vrec:   id is field id in record with }
               cdspl: addrrange); {    variable address }
        vrec: (vdspl: addrrange);
        blck: (bname: ctp);       { block id }
        rec: ()
    end;                          {  --> procedure withstatement }

                                  { error messages: }
                                  { *************** }

  errinx: 0..10;                  { nr of errors in current source line }
  errlist:
  array[1..10] of
    packed record
      pos: Integer;
      nmr: 1..500
    end;

                                  { expression compilation: }
                                  { *********************** }

  gattr: attr;                    { describes the expr currently compiled }

                                  { structured constants: }
                                  { ********************* }

  constbegsys, simptypebegsys, typebegsys, blockbegsys, selectsys, facbegsys,
    statbegsys, typedels: setofsys;
  chartp: array[subchar] of chtp;
  rw: array[1..maxres { nr. of res. words }] of restr;
  frw: array[1..10] of 1..36 { nr. of res. words + 1 };
  rsy: array[1..maxres { nr. of res. words }] of symbol;
  ssy: array[subchar] of symbol;
  rop: array[1..maxres { nr. of res. words }] of operator;
  sop: array[subchar] of operator;
  na: array[1..maxstd] of restr;
  mn: array[0..maxins] of packed array[1..4] of Char;
  sna: array[1..maxsp] of packed array[1..4] of Char;
  cdx: array[0..maxins] of Integer;
  cdxs: array[1..6, 1..7] of Integer;
  pdx: array[1..maxsp] of Integer;
  ordint: array[subchar] of Integer;

  intlabel, mxint10: Integer;
  inputhdf: Boolean; { 'input' appears in header files }
  outputhdf: Boolean; { 'output' appears in header files }
  errtbl: array[1..500] of Boolean; { error occrence tracking }
  toterr: Integer; { total errors in program }

  { Recycling tracking counters, used to check for New/Dispose mismatches. }
  strcnt: Integer; { strings }
  cspcnt: Integer; { constants }
  stpcnt: Integer; { structures }
  ctpcnt: Integer; { identifiers }
  lbpcnt: Integer; { label counts }
  filcnt: Integer; { file tracking counts }
  cipcnt: Integer; { case entry tracking counts }

  f: Boolean; { flag for if error number list entries were printed }
  i: 1..500; { index for error number tracking array }
  c: Char;
  SrcFile, DstFile: string;

{ ------------------------------------------------------------------------- }

                           { for Delphi }

{ ------------------------------------------------------------------------- }

function CurrentChar(var F: Text): WideChar;
begin
  Eoln(F);
  Result := WideChar((TTextRec(F).BufPtr + TTextRec(F).BufPos)^);
end { CurrentChar };

function Mod2(a, n: Integer): Integer;
begin
  if n = 0 then
    Result := a
  else
    Result := a - Floor(Extended(a / n)) * n;
end { Mod2 };

{ ------------------------------------------------------------------------- }

                           { type change }

{ ------------------------------------------------------------------------- }

function stptoint(p: stp): Integer;
var
  r: record
       case Boolean of
         False: (p: stp);
         True: (i: Integer)
       end;
begin
  r.p := p;
  stptoint := r.i
end { stptoint };

function ctptoint(p: ctp): Integer;
var
  r: record
       case Boolean of
         False: (p: ctp);
         True: (i: Integer)
       end;
begin
  r.p := p;
  ctptoint := r.i
end { ctptoint };

{ ------------------------------------------------------------------------- }

                           { recycling controls }

{ ------------------------------------------------------------------------- }

{ get string quanta }

procedure getstr(var p: strvsp);
begin
  New(p); { get New entry }
  strcnt := strcnt + 1 { count }
end { getstr };

{ recycle string quanta list }

procedure putstrs(p: strvsp);
var
  p1: strvsp;
begin
  while p <> nil do
  begin
    p1 := p;
    p := p^.next;
    Dispose(p1);
    strcnt := strcnt - 1
  end
end { putstrs };

{ get label entry }

procedure getlab(var p: lbp);
begin
  New(p); { get New entry }
  lbpcnt := lbpcnt + 1 { add to count }
end { getlab };

{ recycle label entry }

procedure putlab(p: lbp);
begin
  Dispose(p); { release entry }
  lbpcnt := lbpcnt - 1 { remove from count }
end { putlab };

{ push constant entry to list }

procedure pshcst(p: csp);
begin
  { push to constant list }
  p^.next := display[top].fconst;
  display[top].fconst := p;
  cspcnt := cspcnt + 1 { count entries }
end { pshcst };

{ recycle constant entry }

procedure putcst(p: csp);
begin
  { recycle string if present }
  if p^.cclass = strg then
    putstrs(p^.sval)
  else if p^.cclass = reel then
    putstrs(p^.rval);
  Dispose(p); { release entry }
  cspcnt := cspcnt - 1 { remove from count }
end { putcst };

{ push structure entry to list }

procedure pshstc(p: stp);
begin
  { push to structures list }
  p^.next := display[top].fstruct;
  display[top].fstruct := p;
  stpcnt := stpcnt + 1 { count entries }
end { pshstc };

{ recycle structure entry }

procedure putstc(p: stp);
begin
  Dispose(p); { release entry }
  stpcnt := stpcnt - 1
end { putstc };

{ initialize and register identifier entry }

procedure ininam(p: ctp);
begin
  ctpcnt := ctpcnt + 1; { count entry }
  p^.keep := False; { clear keepme flag }
  p^.refer := False { clear referred flag }
end { ininam };

{ recycle identifier entry }

procedure putnam(p: ctp);
var
  p1: ctp;
begin
  if (p^.klass = proc) or (p^.klass = func) then
    while p^.pflist <> nil do
    begin
      { scavenge the parameter list }
      p1 := p^.pflist;
      p^.pflist := p1^.next;
      putnam(p1) { release }
    end;
  putstrs(p^.name); { release name string }
  Dispose(p); { release entry }
  ctpcnt := ctpcnt - 1 { remove from count }
end { putnam };

{ recycle identifier tree }

procedure putnams(p: ctp);
begin
  if p <> nil then
  begin
    putnams(p^.llink); { release left }
    putnams(p^.rlink); { release right }
    { "keep" means it is a parameter and stays with it's procedure or
      function entry. }
    if not p^.keep then
      putnam(p) { release the id entry }
  end
end { putnams };

{ scrub display level }

procedure putdsp(l: disprange);
var
  llp: lbp;
  lvp: csp;
  lsp: stp;
  { release substructure }
  procedure putsub(p: stp);
  var
    p1: stp;
  begin
    { clear record recycle list if record }
    if p^.form = records then
    begin
      { clear structure list }
      while p^.recyc <> nil do
      begin
        { remove top of list }
        p1 := p^.recyc;
        p^.recyc := p1^.next;
        putsub(p1) { release that element }
      end;
      putnams(p^.fstfld) { clear id list }
    end
    else if p^.form = tagfld then
    begin
      if p^.tagfieldp <> nil then
        { recycle anonymous tag fields }
        if p^.tagfieldp^.name = nil then
          putnam(p^.tagfieldp)
    end;
    putstc(p) { release head entry }
  end { putsub };
begin
  putnams(display[l].fname); { Dispose of identifier tree }
  { Dispose of label list }
  while display[l].flabel <> nil do
  begin
    llp := display[l].flabel;
    display[l].flabel := llp^.nextlab;
    putlab(llp)
  end;
  { Dispose of constant list }
  while display[l].fconst <> nil do
  begin
    lvp := display[l].fconst;
    display[l].fconst := lvp^.next;
    putcst(lvp)
  end;
  { Dispose of structure list }
  while display[l].fstruct <> nil do
  begin
    { remove top from list }
    lsp := display[l].fstruct;
    display[l].fstruct := lsp^.next;
    putsub(lsp)
  end
end { putdsp };

{ scrub all display levels until given }

procedure putdsps(l: disprange);
var
  t: disprange;
begin
  if l > top then
  begin
    Writeln(ERROR_HEADER);
    Abort
  end;
  t := top;
  while t > l do
  begin
    putdsp(t);
    t := t - 1
  end
end { putdsps };

{ get external file entry }

procedure getfil(var p: extfilep);
begin
  New(p); { get New entry }
  filcnt := filcnt + 1 { count entry }
end { getfil };

{ recycle external file entry }

procedure putfil(p: extfilep);
begin
  Dispose(p); { release entry }
  filcnt := filcnt - 1 { count entry }
end { putfil };

{ get case tracking entry }

procedure getcas(var p: cip);
begin
  New(p); { get New entry }
  cipcnt := cipcnt + 1 { count entry }
end { getcas };

{ recycle case tracking entry }

procedure putcas(p: cip);
begin
  Dispose(p); { release entry }
  cipcnt := cipcnt - 1 { count entry }
end { putcas };

{ ------------------------------------------------------------------------- }

                { character and string quanta functions }

{ ------------------------------------------------------------------------- }

{ find lower case of character }

function lcase(c: Char): Char;
begin
  if CharInSet(c, ['A'..'Z']) then
    c := Chr(Ord(c) - Ord('A') + Ord('a'));
  lcase := c
end { lcase };

{ find reserved word string equal to id string }

function strequri(a: restr; var b: idstr): Boolean;
var
  m: Boolean;
  i: Integer;
begin
  m := True;
  for i := 1 to reslen do
    if lcase(a[i]) <> lcase(b[i]) then
      m := False;
  for i := reslen + 1 to maxids do
    if b[i] <> ' ' then
      m := False;
  strequri := m
end { equstr };

{ Write variable length id string to Output }

procedure writev(var f: text; s: strvsp; fl: Integer);
var
  i: Integer;
  c: Char;
begin
  i := 1;
  while fl > 0 do
  begin
    c := ' ';
    if s <> nil then
    begin
      c := s^.str[i];
      i := i + 1
    end;
    Write(f, c);
    fl := fl - 1;
    if i > varsqt then
    begin
      s := s^.next;
      i := 1
    end
  end
end { writev };

{ find padded length of variable length id string }

function lenpv(s: strvsp): Integer;
var
  i, l, lc: Integer;
begin
  l := 1;
  lc := 0;
  while s <> nil do
  begin
    for i := 1 to varsqt do
    begin
      if s^.str[i] <> ' ' then
        lc := l;
      l := l + 1; { count characters }
    end;
    s := s^.next
  end;
  lenpv := lc
end { lenpv };

{ assign identifier fixed to variable length string, including allocation }

procedure strassvf(var a: strvsp; var b: idstr);
var
  i, j, l: Integer;
  p, lp: strvsp;
begin
  l := maxids;
  p := nil;
  a := nil;
  j := 1;
  lp := nil;
  while (l > 1) and (b[l] = ' ') do
    l := l - 1; { find length of fixed string }
  if b[l] = ' ' then
    l := 0;
  for i := 1 to l do
  begin
    if j > varsqt then
      p := nil;
    if p = nil then
    begin
      getstr(p);
      p^.next := nil;
      j := 1;
      if a = nil then
        a := p
      else
        lp^.next := p;
      lp := p
    end;
    p^.str[j] := b[i];
    j := j + 1
  end;
  if p <> nil then
    for j := j to varsqt do
      p^.str[j] := ' '
end { strassvf };

{ assign reserved word fixed to variable length string, including allocation }

procedure strassvr(var a: strvsp; b: restr);
var
  i, j, l: Integer;
  p, lp: strvsp;
begin
  l := reslen;
  p := nil;
  a := nil;
  lp := nil;
  j := 1;
  while (l > 1) and (b[l] = ' ') do
    l := l - 1; { find length of fixed string }
  if b[l] = ' ' then
    l := 0;
  for i := 1 to l do
  begin
    if j > varsqt then
      p := nil;
    if p = nil then
    begin
      getstr(p);
      p^.next := nil;
      j := 1;
      if a = nil then
        a := p
      else
        lp^.next := p;
      lp := p
    end;
    p^.str[j] := b[i];
    j := j + 1
  end;
  if p <> nil then
    for j := j to varsqt do
      p^.str[j] := ' '
end { strassvr };

{ assign number string fixed to variable length string, including allocation }

procedure strassvd(var a: strvsp; b: nmstr);
var
  i, j, l: Integer;
  p, lp: strvsp;
begin
  l := digmax;
  p := nil;
  a := nil;
  lp := nil;
  j := 1;
  while (l > 1) and (b[l] = ' ') do
    l := l - 1; { find length of fixed string }
  if b[l] = ' ' then
    l := 0;
  for i := 1 to l do
  begin
    if j > varsqt then
      p := nil;
    if p = nil then
    begin
      getstr(p);
      p^.next := nil;
      j := 1;
      if a = nil then
        a := p
      else
        lp^.next := p;
      lp := p
    end;
    p^.str[j] := b[i];
    j := j + 1
  end;
  if p <> nil then
    for j := j to varsqt do
      p^.str[j] := ' '
end { strassvd };

{ assign constant string fixed to variable length string, including allocation }

procedure strassvc(var a: strvsp; b: csstr; l: Integer);
var
  i, j: Integer;
  p, lp: strvsp;
begin
  p := nil;
  a := nil;
  lp := nil;
  j := 1;
  for i := 1 to l do
  begin
    if j > varsqt then
      p := nil;
    if p = nil then
    begin
      getstr(p);
      p^.next := nil;
      j := 1;
      if a = nil then
        a := p
      else
        lp^.next := p;
      lp := p
    end;
    p^.str[j] := b[i];
    j := j + 1
  end;
  if p <> nil then
    for j := j to varsqt do
      p^.str[j] := ' '
end { strassvc };

{ assign variable length string to fixed identifier }

procedure strassfv(var a: idstr; b: strvsp);
var
  i, j: Integer;
begin
  for i := 1 to maxids do
    a[i] := ' ';
  i := 1;
  while b <> nil do
  begin
    for j := 1 to varsqt do
    begin
      a[i] := b^.str[j];
      i := i + 1
    end;
    b := b^.next
  end
end { strassfv };

{ compare variable length id strings }

function strequvv(a, b: strvsp): Boolean;
var
  m: Boolean;
  i: Integer;
begin
  m := True;
  while (a <> nil) and (b <> nil) do
  begin
    for i := 1 to varsqt do
      if lcase(a^.str[i]) <> lcase(b^.str[i]) then
        m := False;
    a := a^.next;
    b := b^.next
  end;
  if a <> b then
    m := False;
  strequvv := m
end { strequvv };

{ compare variable length id strings, a < b }

function strltnvv(a, b: strvsp): Boolean;
var
  i: Integer;
  ca, cb: Char;
begin
  ca := ' ';
  cb := ' ';
  while (a <> nil) or (b <> nil) do
  begin
    i := 1;
    while (i <= varsqt) and ((a <> nil) or (b <> nil)) do
    begin
      if a <> nil then
        ca := lcase(a^.str[i])
      else
        ca := ' ';
      if b <> nil then
        cb := lcase(b^.str[i])
      else
        cb := ' ';
      if ca <> cb then
      begin
        a := nil;
        b := nil
      end;
      i := i + 1
    end;
    if a <> nil then
      a := a^.next;
    if b <> nil then
      b := b^.next
  end;
  strltnvv := ca < cb
end { strltnvv };

{ compare variable length id string to fixed }

function strequvf(a: strvsp; var b: idstr): Boolean;
var
  m: Boolean;
  i, j: Integer;
  c: Char;
begin
  m := True;
  j := 1;
  for i := 1 to maxids do
  begin
    c := ' ';
    if a <> nil then
    begin
      c := a^.str[j];
      j := j + 1
    end;
    if lcase(c) <> lcase(b[i]) then
      m := False;
    if j > varsqt then
    begin
      a := a^.next;
      j := 1
    end
  end;
  strequvf := m
end { strequvf };

{ compare variable length id string to fixed, a < b }

function strltnvf(a: strvsp; var b: idstr): Boolean;
var
  i, j, f: Integer;
  c: Char;
begin
  i := 1;
  j := 1;
  c := ' ';
  f := 0;
  while i < maxids do
  begin
    c := ' ';
    if a <> nil then
    begin
      c := a^.str[j];
      j := j + 1
    end;
    if lcase(c) <> lcase(b[i]) then
    begin
      f := i;
      i := maxids
    end
    else
      i := i + 1;
    if j > varsqt then
    begin
      a := a^.next;
      j := 1
    end
  end;
  strltnvf := lcase(c) < lcase(b[f])
end { strltnvf };

{ get character from variable length string }

function strchr(a: strvsp; x: Integer): Char;
var
  c: Char;
  i: Integer;
  q: Integer;
begin
  c := ' ';
  i := 1;
  q := 1;
  while i < x do
  begin
    if q >= varsqt then
    begin
      q := 1;
      if a <> nil then
        a := a^.next
    end
    else
      q := q + 1;
    i := i + 1
  end;
  if a <> nil then
    c := a^.str[q];
  strchr := c
end { strchr };

{ put character to variable length string }

procedure strchrass(var a: strvsp; x: Integer; c: Char);
var
  i: Integer;
  q: Integer;
  p, l: strvsp;
  procedure getsqt;
  var
    y: Integer;
  begin
    if p = nil then
    begin
      getstr(p);
      for y := 1 to varsqt do
        p^.str[y] := ' ';
      p^.next := nil;
      if a = nil then
        a := p
      else
        l^.next := p
    end
  end { getsqt };
begin
  i := 1;
  q := 1;
  p := a;
  l := nil;
  getsqt;
  while i < x do
  begin
    if q >= varsqt then
    begin
      q := 1;
      l := p;
      p := p^.next;
      getsqt
    end
    else
      q := q + 1;
    i := i + 1
  end;
  p^.str[q] := c
end { strchrass };

{ ------------------------------------------------------------------------- }

  { dump the display }

procedure prtdsp;
var
  i: Integer;
  procedure prtlnk(p: ctp; f: Integer);
  var
    i: Integer;
  begin
    if p <> nil then
    begin
      for i := 1 to f do
        Write(' ');
      writev(Output, p^.name, 10);
      Writeln;
      if p^.llink <> nil then
        prtlnk(p^.llink, f + 3);
      if p^.rlink <> nil then
        prtlnk(p^.rlink, f + 3)
    end
  end { prtlnk };
begin
  Writeln;
  Writeln('Display:');
  Writeln;
  for i := 0 to displimit do
    if display[i].fname <> nil then
    begin

      Writeln('level ', i: 1);
      Writeln;
      prtlnk(display[i].fname, 0);
      Writeln

    end;
  Writeln;
end { prtdsp };

procedure endofline;
var
  lastpos, freepos, currpos, currnmr, f, k: Integer;
begin
  if errinx > 0 then { Output error messages }
  begin
    Write(Output, linecount: 6, ' ****  ': 9);
    lastpos := -1;
    freepos := 1;
    for k := 1 to errinx do
    begin
      with errlist[k] do
      begin
        currpos := pos;
        currnmr := nmr
      end;
      if currpos = lastpos then
        Write(Output, ',')
      else
      begin
        while freepos < currpos do
        begin
          Write(Output, ' ');
          freepos := freepos + 1
        end;
        Write(Output, '^');
        lastpos := currpos
      end;
      if currnmr < 10 then
        f := 1
      else if currnmr < 100 then
        f := 2
      else
        f := 3;
      Write(Output, currnmr: f);
      freepos := freepos + f + 1
    end;
    Writeln(Output);
    errinx := 0
  end;
  linecount := linecount + 1;
  if list and (not Eof(prd)) then
  begin
    Write(Output, linecount: 6, '  ': 2);
    if dp then
      Write(Output, lc: 7)
    else
      Write(Output, ic: 7);
    Write(Output, ' ')
  end;
  { Output line marker in intermediate file }
  if not Eof(prd) then
  begin
    if prcode then
      Writeln(prr, ':', linecount: 1);
  end;
  chcnt := 0
end { endofline };

procedure errmsg(ferrnr: Integer);
begin
  case ferrnr of
    1:   Write('Error in simple type');
    2:   Write('Identifier expected');
    3:   Write('''program'' expected');
    4:   Write(''')'' expected');
    5:   Write(''':'' expected');
    6:   Write('Illegal symbol');
    7:   Write('Error in parameter list');
    8:   Write('''of'' expected');
    9:   Write('''('' expected');
    10:  Write('Error in type');
    11:  Write('''['' expected');
    12:  Write(''']'' expected');
    13:  Write('''end'' expected');
    14:  Write(''';'' expected');
    15:  Write('Integer expected');
    16:  Write('''='' expected');
    17:  Write('''begin'' expected');
    18:  Write('Error in declaration part');
    19:  Write('Error in field-list');
    20:  Write(''','' expected');
    21:  Write('''.'' expected');

    50:  Write('Error in constant');
    51:  Write(''':='' expected');
    52:  Write('''then'' expected');
    53:  Write('''until'' expected');
    54:  Write('''do'' expected');
    55:  Write('''to''/''downto'' expected');
    56:  Write('''if'' expected');
    57:  Write('''file'' expected');
    58:  Write('Error in factor');
    59:  Write('Error in variable');

    101: Write('Identifier declared twice');
    102: Write('Low bound exceeds highbound');
    103: Write('Identifier is not of appropriate class');
    104: Write('Identifier not declared');
    105: Write('Sign not allowed');
    106: Write('Number expected');
    107: Write('Incompatible subrange types');
    109: Write('Type must not be real');
    110: Write('Tagfield type must be scalar or subrange');
    111: Write('Incompatible with tagfield type');
    112: Write('Index type must not be real');
    113: Write('Index type must be scalar or subrange');
    114: Write('Base type must not be real');
    115: Write('Base type must be scalar or subrange');
    116: Write('Error in type of standard procedure parameter');
    117: Write('Unsatisfied forward reference');
    118: Write('Forward reference type identifier in variable declaration');
    119: Write('Forward declared; repetition of parameter list not allowed');
    120: Write('Function result type must be scalar, subrange or point');
    121: Write('File value parameter, or parameter containing file, not allowed');
    122: Write('Forward declared function; repetition of result type not allowed');
    123: Write('Missing result type in function declaration');
    124: Write('F-format for real only');
    125: Write('Error in type of standard function parameter');
    126: Write('Number of parameters does not agree with declaration');
    127: Write('Illegal parameter substitution');
    128: Write('Result type of parameter function does not agree with declaration');
    129: Write('Type conflict of operands');
    130: Write('Expression is not of set type');
    131: Write('Tests on equality allowed only');
    132: Write('Strict inclusion not allowed');
    133: Write('File comparison not allowed');
    134: Write('Illegal type of operand(s)');
    135: Write('Type of operand must be Boolean');
    136: Write('Set element type must be scalar or subrange');
    137: Write('Set element types not compatible');
    138: Write('Type of variable is not array');
    139: Write('Index type is not compatible with declaration');
    140: Write('Type of variable is not record');
    141: Write('Type of variable must be file or pointer');
    142: Write('Illegal parameter substitution');
    143: Write('Illegal type of loop control variable');
    144: Write('Illegal type of expression');
    145: Write('Type conflict');
    146: Write('Assignment of files not allowed');
    147: Write('Label type incompatible with selecting expression');
    148: Write('Subrange bounds must be scalar');
    149: Write('Index type must not be integer');
    150: Write('Assignment to standard function is not allowed');
    151: Write('Assignment to formal function is not allowed');
    152: Write('No such field in this record');
    153: Write('Type error in read');
    154: Write('Actual parameter must be a variable');
    155: Write('Control variable must ~ot be declared on intermediate');
    156: Write('Multidefined case label');
    157: Write('Too many cases in case statement');
    158: Write('Missing corresponding variant declaration');
    159: Write('Real or string tagfields not allowed');
    160: Write('Previous declaration was not forward');
    161: Write('Again forward declared');
    162: Write('Parameter size must be constant');
    163: Write('Missing variant in declaration');
    164: Write('Substitution of standard proc/func not allowed');
    165: Write('Multidefined label');
    166: Write('Multideclared label');
    167: Write('Undeclared label');
    168: Write('Undefined label');
    169: Write('Error in base set');
    170: Write('Value parameter expected');
    171: Write('Standard file was redeclared');
    172: Write('Undeclared external file');
    173: Write('Fortran procedure or function expected');
    174: Write('Pascal procedure or function expected');
    175: Write('Missing file "input" in program heading');
    176: Write('Missing file "output" in program heading');
    177: Write('Assiqnment to function identifier not allowed here');
    178: Write('Multidefined record variant');
    179: Write('X-opt of actual proc/funcdoes not match formal declaration');
    180: Write('Control variable must not be formal');
    181: Write('Constant part of address out of ranqe');
    182: Write('identifier too long');
    183: Write('For index variable must be local to this block');
    184: Write('Interprocedure goto does not reference outter block of destination');
    185: Write('Goto references deeper nested statement');
    186: Write('Label referenced by goto at lesser statement level or ' +
               'differently nested statement');
    187: Write('Goto references label in different nested statement');
    188: Write('Label referenced by goto in different nested statement');
    189: Write('Parameter lists of formal and actual parameters not congruous');
    190: Write('File component may not contain other files');
    191: Write('Cannot assign from file or component containing files');
    192: Write('Assignment to function that is not active');
    193: Write('Function does not assign to result');
    194: Write('Exponent too large');
    195: Write('For loop index is threatened');
    197: Write('Var parameter cannot be packed');
    198: Write('Var parameter cannot be a tagfield');
    199: Write('Var parameter must be same type');

    201: Write('Error in real constant: digit expected');
    202: Write('String constant must not exceed source line');
    203: Write('Integer constant exceeds range');
    204: Write('8 or 9 in octal number');
    205: Write('Zero string not allowed');
    206: Write('Integer part of real constant exceeds ranqe');

    250: Write('Too many nestedscopes of identifiers');
    251: Write('Too many nested procedures and/or functions');
    252: Write('Too many forward references of procedure entries');
    253: Write('Procedure too long');
    254: Write('Too many long constants in this procedure');
    255: Write('Too many errors on this source line');
    256: Write('Too many external references');
    257: Write('Too many externals');
    258: Write('Too many local files');
    259: Write('Expression too complicated');
    260: Write('Too many exit labels');
    261: Write('Label beyond valid integral value (>9999)');

    300: Write('Division by zero');
    301: Write('No case provided for this value');
    302: Write('Index expression out of bounds');
    303: Write('Value to be assigned is out of bounds');
    304: Write('Element expression out of range');

    398: Write('Implementation restriction');
    399: Write('Feature not implemented');

    400,
    500: Write('Compiler internal error');
  end
end { errmsg };

procedure error(ferrnr: Integer);
begin
  { This diagnostic is here because error buffers error numbers til the end
    of line, and sometimes you need to know exactly where they occurred. }
  {
  Writeln; Writeln('error: ', ferrnr:1);
  }
  errtbl[ferrnr] := True; { track this error }
  if errinx >= 9 then
  begin
    errlist[10].nmr := 255;
    errinx := 10
  end
  else
  begin
    errinx := errinx + 1;
    errlist[errinx].nmr := ferrnr
  end;
  errlist[errinx].pos := chcnt;
  toterr := toterr + 1
end { error };

procedure insymbol;
{ Read next basic symbol of source program and return its
description in the global variables sy, op, id, val and lgth }
label
  1;
var
  i, k: Integer;
  digit: nmstr; { temp holding for digit string }
  rvalb: nmstr; { temp holding for real string }
  passtr: csstr;
  lvp: csp;
  test, ferr: Boolean;
  iscmte: Boolean;
  ev: Integer;

  procedure nextch;
  begin
{$IFDEF MSWINDOWS}
    if CurrentChar(prd) = #$0A then
    begin
      Read(prd, ch);
      Exit;
    end;
{$ENDIF}
    if eol then
    begin
      if list then
        Writeln(Output);
      endofline
    end;
    if not Eof(prd) then
    begin
      eol := Eoln(prd);
      Read(prd, ch);
      if list then
        Write(Output, ch);
      chcnt := chcnt + 1
    end
    else if (sy <> endsy) or (ch <> '.') then
    begin
      Writeln(Output, '   *** eof ', 'encountered');
      test := False
    end
  end { nextch };

  procedure options;
  var
    ch1: Char;
    dummy: Boolean;
    procedure switch(var opt: Boolean);
    begin
      nextch;
      if (ch = '+') or (ch = '-') then
      begin
        opt := ch = '+';
        option[ch1] := opt;
        if prcode then
          Writeln(prr, 'o ', ch1, ch);
        nextch;
      end
    end { switch };
  begin
    repeat
      nextch;
      ch1 := lcase(ch);
      if ch1 = 't' then
        switch(prtables)
      else if ch1 = 'l' then
      begin
        switch(list);
        if not list then
          Writeln(Output)
      end
      else if ch1 = 'd' then
      begin
        switch(debug);
      end
      else if ch1 = 'c' then
        switch(prcode)
      else if ch1 = 'v' then
        switch(chkvar)
      else if ch1 = 'r' then
        switch(chkref)
      else if ch1 = 'u' then
        switch(chkudtc)
      else if CharInSet(ch1, ['a'..'z']) then
        switch(dummy) { pass through unknown options }
      else
      begin
        { skip all likely option chars }
        while CharInSet(ch, ['a'..'z', 'A'..'Z', '+', '-', '0'..'9', '_']) do
          nextch;
      end;
    until ch <> ',';
  end { options };

begin
  1:
  { Skip both spaces and controls. This allows arbitrary formatting characters
    in the source. }
  repeat
    while (ch <= ' ') and not eol do
      nextch;
    test := eol;
    if test then
      nextch
  until not test;
  if chartp[ch] = illegal then
  begin
    sy := othersy;
    op := noop;
    error(399);
    nextch
  end
  else
    case chartp[ch] of
      letter:
        begin
          k := 0;
          ferr := True;
          repeat
            if k < maxids then
            begin
              k := k + 1;
              id[k] := ch
            end
            else if ferr then
            begin
              error(182);
              ferr := False
            end;
            nextch
          until chartp[ch] in [special, illegal, chstrquo, chcolon,
            chperiod, chlt, chgt, chlparen, chspace, chlcmt];
          if k >= kk then
            kk := k
          else
            repeat
              id[kk] := ' ';
              kk := kk - 1
            until kk = k;
          sy := ident;
          op := noop;
          if k <= reslen then
            for i := frw[k] to frw[k + 1] - 1 do
              if strequri(rw[i], id) then
              begin
                sy := rsy[i];
                op := rop[i]
              end;
        end;
      number:
        begin
          op := noop;
          i := 0;
          repeat
            i := i + 1;
            if i <= digmax then
              digit[i] := ch;
            nextch
          until chartp[ch] <> number;
          if ((ch = '.') and (CurrentChar(prd) <> '.') and (CurrentChar(prd) <>
            ')')) or
            (lcase(ch) = 'e') then
          begin
            k := i;
            if ch = '.' then
            begin
              k := k + 1;
              if k <= digmax then
                digit[k] := ch;
              nextch; { if ch = '.' then begin ch := ':'; goto 3 end; }
              if chartp[ch] <> number then
                error(201)
              else
                repeat
                  k := k + 1;
                  if k <= digmax then
                    digit[k] := ch;
                  nextch
                until chartp[ch] <> number
            end;
            if lcase(ch) = 'e' then
            begin
              k := k + 1;
              if k <= digmax then
                digit[k] := ch;
              nextch;
              if (ch = '+') or (ch = '-') then
              begin
                k := k + 1;
                if k <= digmax then
                  digit[k] := ch;
                nextch
              end;
              if chartp[ch] <> number then
                error(201)
              else
              begin
                ev := 0;
                ferr := True;
                repeat
                  k := k + 1;
                  if k <= digmax then
                    digit[k] := ch;
                  nextch;
                  if ferr then
                  begin
                    if ev <= mxint10 then
                      ev := ev * 10 + ordint[digit[k]]
                    else
                    begin
                      error(194);
                      ferr := False
                    end
                  end
                until chartp[ch] <> number
              end
            end;
            New(lvp);
            pshcst(lvp);
            sy := realconst;
            lvp^.cclass := reel;
            with lvp^ do
            begin
              for i := 1 to digmax do
                rvalb[i] := ' ';
              if k <= digmax then
                for i := 2 to k + 1 do
                  rvalb[i] := digit[i - 1]
              else
              begin
                error(203);
                rvalb[2] := '0';
                rvalb[3] := '.';
                rvalb[4] := '0'
              end;
              { place buffered real string in constant }
              strassvd(rval, rvalb)
            end;
            val.valp := lvp
          end
          else
          begin
            if i > digmax then
            begin
              error(203);
              val.ival := 0
            end
            else
              with val do
              begin
                ival := 0;
                for k := 1 to i do
                begin
                  if ival <= mxint10 then
                    ival := ival * 10 + ordint[digit[k]]
                  else
                  begin
                    error(203);
                    ival := 0
                  end
                end;
                sy := intconst
              end
          end
        end;
      chstrquo:
        begin
          lgth := 0;
          sy := stringconst;
          op := noop;
          for i := 1 to strglgth do
            passtr[i] := ' ';
          repeat
            repeat
              nextch;
              lgth := lgth + 1;
              if lgth <= strglgth then
                passtr[lgth] := ch
            until (eol) or (ch = '''');
            if eol then
              error(202)
            else
              nextch
          until ch <> '''';
          passtr[lgth] := ' '; { get rid of trailing quote }
          lgth := lgth - 1; { now lgth = nr of chars in string }
          if lgth = 1 then
            val.ival := Ord(passtr[1])
          else
          begin
            if lgth = 0 then
              error(205);
            New(lvp);
            pshcst(lvp);
            lvp^.cclass := strg;
            if lgth > strglgth then
            begin
              error(399);
              lgth := strglgth
            end;
            with lvp^ do
            begin
              slgth := lgth;
              strassvc(sval, passtr, strglgth)
            end;
            val.valp := lvp
          end
        end;
      chcolon:
        begin
          op := noop;
          nextch;
          if ch = '=' then
          begin
            sy := becomes;
            nextch
          end
          else
            sy := colon
        end;
      chperiod:
        begin
          op := noop;
          nextch;
          if Eof(Prd) then
            sy := period
          else if ch = '.' then
          begin
            sy := range;
            nextch
          end
          else if ch = ')' then
          begin
            sy := rbrack;
            nextch
          end
          else
            sy := period
        end;
      chlt:
        begin
          nextch;
          sy := relop;
          if ch = '=' then
          begin
            op := leop;
            nextch
          end
          else if ch = '>' then
          begin
            op := neop;
            nextch
          end
          else
            op := ltop
        end;
      chgt:
        begin
          nextch;
          sy := relop;
          if ch = '=' then
          begin
            op := geop;
            nextch
          end
          else
            op := gtop
        end;
      chlparen:
        begin
          nextch;
          if ch = '*' then
          begin
            nextch;
            if ch = '$' then
              options;
            repeat
              while (ch <> '}') and (ch <> '*') and not Eof(prd) do
                nextch;
              iscmte := ch = '}';
              nextch
            until iscmte or (ch = ')') or Eof(prd);
            if not iscmte then
              nextch;
            goto 1
          end
          else if ch = '.' then
          begin
            sy := lbrack;
            nextch
          end
          else
            sy := lparent;
          op := noop
        end;
      chlcmt:
        begin
          nextch;
          if ch = '$' then
            options;
          repeat
            while (ch <> '}') and (ch <> '*') and not Eof(prd) do
              nextch;
            iscmte := ch = '}';
            nextch
          until iscmte or (ch = ')') or Eof(prd);
          if not iscmte then
            nextch;
          goto 1
        end;
      special:
        begin
          sy := ssy[ch];
          op := sop[ch];
          nextch
        end;
      chspace: sy := othersy
    end;

  if dodmplex then
  begin { lexical dump }

    Writeln;
    Write('symbol: ');
    case sy of
      ident:
        Write('ident: ', string(id): 10);
      intconst:
        Write('int const: ', val.ival: 1);
      realconst:
        begin
          Write('real const: ');
          writev(Output, val.valp^.rval, 9)
        end;
      stringconst:
        begin
          Write('string const: ''');
          writev(Output, val.valp^.sval, val.valp^.slgth);
          Write('''')
        end;
      notsy:
        Write('not');
      mulop:
        Write('*');
      addop:
        Write('+');
      relop:
        Write('<');
      lparent:
        Write('(');
      rparent:
        Write(')');
      lbrack:
        Write('[');
      rbrack:
        Write(']');
      comma:
        Write(',');
      semicolon:
        Write(';');
      period:
        Write('.');
      arrow:
        Write('^');
      colon:
        Write(':');
      becomes:
        Write(':=');
      range:
        Write('..');
      labelsy:
        Write('label');
      constsy:
        Write('const');
      typesy:
        Write('type');
      varsy:
        Write('var');
      funcsy:
        Write('function');
      progsy:
        Write('program');
      procsy:
        Write('procedure');
      setsy:
        Write('set');
      packedsy:
        Write('packed');
      arraysy:
        Write('array');
      recordsy:
        Write('record');
      filesy:
        Write('file');
      beginsy:
        Write('begin');
      ifsy:
        Write('if');
      casesy:
        Write('case');
      repeatsy:
        Write('repeat');
      whilesy:
        Write('while');
      forsy:
        Write('for');
      withsy:
        Write('with');
      gotosy:
        Write('goto');
      endsy:
        Write('end');
      elsesy:
        Write('else');
      untilsy:
        Write('until');
      ofsy:
        Write('of');
      dosy:
        Write('do');
      tosy:
        Write('to');
      downtosy:
        Write('downto');
      thensy:
        Write('then');
      othersy:
        Write('<other>');
    end;
    Writeln
  end
end { insymbol };

procedure enterid(fcp: ctp);
{ enter id pointed at by fcp into the name-table,
 which on each declaration level is organised as
 an unbalanced binary tree }
var
  lcp, lcp1: ctp;
  lleft: Boolean;
begin
  lcp := display[top].fname;
  if lcp = nil then
    display[top].fname := fcp
  else
  begin
    repeat lcp1 := lcp;
      if strequvv(lcp^.name, fcp^.name) then { name conflict, follow right link }
      begin
        error(101);
        lcp := lcp^.rlink;
        lleft := False
      end
      else if strltnvv(lcp^.name, fcp^.name) then
      begin
        lcp := lcp^.rlink;
        lleft := False
      end
      else
      begin
        lcp := lcp^.llink;
        lleft := True
      end
    until lcp = nil;
    if lleft then
      lcp1^.llink := fcp
    else
      lcp1^.rlink := fcp
  end;
  fcp^.llink := nil;
  fcp^.rlink := nil
end { enterid };

procedure searchsection(fcp: ctp; var fcp1: ctp);
{ to find record fields and forward declared procedure id's
 --> procedure proceduredeclaration
 --> procedure selector }
label
  1;
begin
  while fcp <> nil do
    if strequvf(fcp^.name, id) then
      goto 1
    else if strltnvf(fcp^.name, id) then
      fcp := fcp^.rlink
    else
      fcp := fcp^.llink;
  1: fcp1 := fcp
end { searchsection };

procedure searchidnenm(fidcls: setofids; var fcp: ctp; var mm: Boolean);
label
  1;
var
  lcp: ctp;
  disxl: disprange;
begin
  mm := False;
  for disxl := top downto 0 do
  begin
    lcp := display[disxl].fname;
    while lcp <> nil do
    begin
      if strequvf(lcp^.name, id) then
        if lcp^.klass in fidcls then
        begin
          disx := disxl;
          goto 1
        end
        else
        begin
          mm := True;
          lcp := lcp^.rlink
        end
      else if strltnvf(lcp^.name, id) then
        lcp := lcp^.rlink
      else
        lcp := lcp^.llink
    end
  end;
  disx := 0;
  lcp := nil; { make sure this is not found }
  1: fcp := lcp
end { searchidnenm };

procedure searchidne(fidcls: setofids; var fcp: ctp);
var
  mm: Boolean;
begin
  searchidnenm(fidcls, fcp, mm);
  if mm then
    error(103)
end { searchidne };

procedure searchid(fidcls: setofids; var fcp: ctp);
label
  1;
var
  lcp: ctp;
begin
  searchidne(fidcls, lcp); { perform no error search }
  if lcp <> nil then
  begin
    lcp^.refer := True;
    goto 1
  end; { found }
  { search not successful
   --> procedure simpletype }
  error(104);
  { to avoid returning nil, reference an entry
   for an undeclared id of appropriate class
   --> procedure enterundecl }
  if types in fidcls then
    lcp := utypptr
  else if vars in fidcls then
    lcp := uvarptr
  else if field in fidcls then
    lcp := ufldptr
  else if konst in fidcls then
    lcp := ucstptr
  else if proc in fidcls then
    lcp := uprcptr
  else
    lcp := ufctptr;
  1: fcp := lcp
end { searchid };

procedure getbounds(fsp: stp; var fmin, fmax: Integer);
{ get internal bounds of subrange or scalar type }
{ assume fsp<>intptr and fsp<>realptr }
begin
  fmin := 0;
  fmax := 0;
  if fsp <> nil then
    with fsp^ do
      if form = subrange then
      begin
        fmin := min.ival;
        fmax := max.ival
      end
      else if fsp = charptr then
      begin
        fmin := ordminchar;
        fmax := ordmaxchar
      end
      else if fsp = intptr then
      begin
        fmin := -maxint;
        fmax := maxint
      end
      else if fconst <> nil then
        fmax := fconst^.values.ival
end { getbounds };

function isbyte(fsp: stp): Boolean;
{ check structure is byte }
var
  fmin, fmax: Integer;
begin
  getbounds(fsp, fmin, fmax);
  isbyte := (fmin >= 0) and (fmax <= 255)
end { isbyte };

function basetype(fsp: stp): stp;
{ remove any subrange types }
begin
  if fsp <> nil then
    while fsp^.form = subrange do
      fsp := fsp^.rangetype;
  basetype := fsp
end { basetype };

{ alignment for general memory placement }

function alignquot(fsp: stp): Integer;
begin
  alignquot := 1;
  if fsp <> nil then
    with fsp^ do
      case form of
        scalar:
          if fsp = intptr then
            alignquot := intal
          else if fsp = boolptr then
            alignquot := boolal
          else if scalkind = declared then
            alignquot := intal
          else if fsp = charptr then
            alignquot := charal
          else if fsp = realptr then
            alignquot := realal
          else { parmptr }
            alignquot := parmal;
        subrange:
          alignquot := alignquot(rangetype);
        pointer:
          alignquot := adral;
        power:
          alignquot := setal;
        files:
          alignquot := fileal;
        arrays:
          alignquot := alignquot(aeltype);
        records:
          alignquot := recal;
        variant,
        tagfld:
          error(501)
      end
end { alignquot };

procedure alignu(fsp: stp; var flc: addrrange);
var
  k, l: Integer;
begin
  k := alignquot(fsp);
  l := flc - 1;
  flc := l + k - Mod2(k + l, k)
end { align };

procedure alignd(fsp: stp; var flc: stkoff);
var
  k, l: Integer;
begin
  k := alignquot(fsp);
  l := flc + 1;
  flc := l - k + Mod2(k - l, k);
end { align };

{ align for stack }

function aligns(flc: addrrange): addrrange;
var
  l: Integer;
begin
  l := flc + 1;
  flc := l - stackal + Mod2(stackal - l, stackal);
  aligns := flc
end { aligns };

procedure printtables(fb: Boolean);
{ print data structure and name table }
var
  i, lim: disprange;

  procedure marker;
    { mark data structure entries to avoid multiple printout }
  var
    i: Integer;

    procedure markctp(fp: ctp); forward;

    procedure markstp(fp: stp);
      { mark data structures, prevent cycles }
    begin
      if fp <> nil then
        with fp^ do
        begin
          marked := True;
          case form of
            scalar:
              ;
            subrange:
              markstp(rangetype);
            pointer:
              { don't mark eltype: cycle possible; will be marked
                anyway, if fp = True };
            power:
              markstp(elset);
            arrays:
              begin
                markstp(aeltype);
                markstp(inxtype)
              end;
            records:
              begin
                markctp(fstfld);
                markstp(recvar)
              end;
            files:
              markstp(filtype);
            tagfld:
              markstp(fstvar);
            variant:
              begin
                markstp(nxtvar);
                markstp(subvar)
              end
          end
        end
    end { markstp };

    procedure markctp;
    begin
      if fp <> nil then
        with fp^ do
        begin
          markctp(llink);
          markctp(rlink);
          markstp(idtype)
        end
    end { markctp };

  begin { marker }
    for i := top downto lim do
      markctp(display[i].fname)
  end { marker };

  procedure followctp(fp: ctp); forward;

  procedure followstp(fp: stp);
  begin
    if fp <> nil then
      with fp^ do
        if marked then
        begin
          marked := False;
          Write('S: ', stptoint(fp): intdig, ' ', size: intdig, ' ');
          case form of
            scalar:
              begin
                Write(Output, 'scalar': intdig, ' ');
                if scalkind = standard then
                  Write(Output, 'standard': intdig)
                else
                  Write(Output, 'declared': intdig, ' ', ctptoint(fconst):
                    intdig);
                Writeln(Output)
              end;
            subrange:
              begin
                Write(Output, 'subrange': intdig, ' ', stptoint(rangetype): intdig, ' ');
                if rangetype <> realptr then
                  Write(Output, min.ival: intdig, ' ', max.ival: intdig)
                else if (min.valp <> nil) and (max.valp <> nil) then
                begin
                  Write(' ');
                  writev(Output, min.valp^.rval, 9);
                  Write(' ');
                  writev(Output, max.valp^.rval, 9)
                end;
                Writeln(Output);
                followstp(rangetype);
              end;
            pointer:
              Writeln(Output, 'pointer': intdig, ' ', stptoint(eltype): intdig);
            power:
              begin
                Writeln(Output, 'set': intdig, ' ', stptoint(elset): intdig);
                followstp(elset)
              end;
            arrays:
              begin
                Writeln(Output, 'array': intdig, ' ', stptoint(aeltype): intdig,
                  ' ', stptoint(inxtype): intdig);
                followstp(aeltype);
                followstp(inxtype)
              end;
            records:
              begin
                Writeln(Output, 'record': intdig, ' ', ctptoint(fstfld): intdig,
                  ' ', stptoint(recvar): intdig);
                followctp(fstfld);
                followstp(recvar)
              end;
            files:
              begin
                Writeln(Output, 'file': intdig, ' ', stptoint(filtype): intdig);
                followstp(filtype)
              end;
            tagfld:
              begin
                Writeln(Output, 'tagfld': intdig, ' ', ctptoint(tagfieldp):
                  intdig, ' ', stptoint(fstvar): intdig);
                followstp(fstvar)
              end;
            variant:
              begin
                Writeln(Output, 'variant': intdig, ' ', stptoint(nxtvar): intdig,
                  ' ', stptoint(subvar): intdig, varval.ival);
                followstp(nxtvar);
                followstp(subvar)
              end
          end
        end
  end { followstp };

  procedure followctp;
  begin
    if fp <> nil then
      with fp^ do
      begin
        Write('C: ', ctptoint(fp): intdig, ' ');
        writev(Output, name, intdig);
        Write(' ', ctptoint(llink): intdig, ' ', ctptoint(rlink): intdig, ' ',
          stptoint(idtype): intdig, ' ');
        case klass of
          types:
            Write(Output, 'type': intdig);
          konst:
            begin
              Write(Output, 'constant': intdig, ' ', ctptoint(next): intdig, ' ');
              if idtype <> nil then
                if idtype = realptr then
                begin
                  if values.valp <> nil then
                  begin
                    writev(Output, values.valp^.rval, 9)
                  end
                end
                else if idtype^.form = arrays then { stringconst }
                begin
                  if values.valp <> nil then
                  begin
                    with values.valp^ do
                      writev(Output, sval, slgth)
                  end
                end
                else
                  Write(Output, values.ival: intdig)
            end;
          vars:
            begin
              Write(Output, 'variable': intdig, ' ');
              if vkind = actual then
                Write(Output, 'actual': intdig)
              else
                Write(Output, 'formal': intdig);
              Write(Output, ' ', ctptoint(next): intdig, ' ', vlev: intdig, ' ',
                vaddr: intdig);
            end;
          field:
            Write(Output, 'field': intdig, ' ', ctptoint(next): intdig, ' ', fldaddr: intdig);
          proc,
            func:
            begin
              if klass = proc then
                Write(Output, 'procedure': intdig, ' ')
              else
                Write(Output, 'function': intdig, ' ');
              if pfdeckind = standard then
                Write(Output, 'standard': intdig, '-', key: intdig)
              else
              begin
                Write(Output, 'declared': intdig, '-', ctptoint(next): intdig, '-');
                Write(Output, pflev: intdig, ' ', pfname: intdig, ' ');
                if pfkind = actual then
                begin
                  Write(Output, 'actual': intdig, ' ');
                  if forwdecl then
                    Write(Output, 'forward': intdig, ' ')
                  else
                    Write(Output, 'notforward': intdig, ' ');
                  if externl then
                    Write(Output, 'extern': intdig)
                  else
                    Write(Output, 'not extern': intdig);
                end
                else
                  Write(Output, 'formal': intdig)
              end
            end
        end;
        Writeln(Output);
        followctp(llink);
        followctp(rlink);
        followstp(idtype)
      end
  end { followctp };

begin
  Writeln(Output);
  Writeln(Output);
  Writeln(Output);
  if fb then
    lim := 0
  else
  begin
    lim := top;
    Write(Output, ' local')
  end;
  Writeln(Output, ' tables:');
  Writeln(Output);
  Writeln('C: ', 'Entry #': intdig, ' ', 'Id': intdig, ' ', 'llink': intdig,
    ' ', 'rlink': intdig, ' ', 'Typ': intdig, ' ', 'Class': intdig);
  Writeln('S: ', 'Entry #': intdig, ' ', 'Size': intdig, ' ', 'Form ': intdig);
  Writeln('===============================================================');
  marker;
  for i := top downto lim do
    followctp(display[i].fname);
  Writeln(Output);
  if not eol then
    Write(Output, ' ': chcnt + 16)
end { printtables };

procedure chkrefs(p: ctp; var w: Boolean);
begin
  if chkref then
  begin
    if p <> nil then
    begin
      chkrefs(p^.llink, w); { check left }
      chkrefs(p^.rlink, w); { check right }
      if not p^.refer then
      begin
        if not w then
          Writeln;
        writev(Output, p^.name, 10);
        Writeln(' unreferenced');
        w := True
      end
    end
  end
end { chkrefs };

procedure genlabel(var nxtlab: Integer);
begin
  intlabel := intlabel + 1;
  nxtlab := intlabel
end { genlabel };

procedure searchlabel(var llp: lbp; level: disprange);
var
  fllp: lbp; { found label entry }
begin
  fllp := nil; { set no label found }
  llp := display[level].flabel; { index top of label list }
  while llp <> nil do
  begin { traverse }
    if llp^.labval = val.ival then
    begin { found }
      fllp := llp; { set entry found }
      llp := nil { stop }
    end
    else
      llp := llp^.nextlab { next in list }
  end;
  llp := fllp { return found entry or nil }
end { searchlabel };

procedure newlabel(var llp: lbp);
var
  lbname: Integer;
begin
  with display[top] do
  begin
    getlab(llp);
    with llp^ do
    begin
      labval := val.ival;
      if labval > 9999 then
        error(261);
      genlabel(lbname);
      defined := False;
      nextlab := flabel;
      labname := lbname;
      vlevel := level;
      slevel := 0;
      ipcref := False;
      minlvl := maxint;
      bact := False;
      refer := False
    end;
    flabel := llp
  end
end { newlabel };

procedure prtlabels;
var
  llp: lbp; { found label entry }
begin
  Writeln;
  Writeln('Labels: ');
  Writeln;
  llp := display[level].flabel; { index top of label list }
  while llp <> nil do
    with llp^ do
    begin { traverse }
      Writeln('label: '    , labval: 1,  ' defined: ', defined,
              ' internal: ', labname: 1, ' vlevel: ' , vlevel: 1,
              ' slevel: '  , slevel: 1,  ' ipcref: ' , ipcref: 1,
              ' minlvl: '  , minlvl: 1);
      Writeln('   bact: '  , bact);
      llp := llp^.nextlab { next in list }
    end
end { prtlabels };

procedure block(fsys: setofsys; fsy: symbol; fprocp: ctp);
var
  lsy: symbol;
  stalvl: Integer; { statement nesting level }

  procedure skip(fsys: setofsys);
    { skip input string until relevant symbol found }
  begin
    if not Eof(prd) then
    begin
      while not (sy in fsys) and (not Eof(prd)) do
        insymbol;
      if not (sy in fsys) then
        insymbol
    end
  end { skip };

  procedure constant(fsys: setofsys; var fsp: stp; var fvalu: valu);
  var
    lsp: stp;
    lcp: ctp;
    sign: (none, pos, neg);
    lvp: csp;
    i: 2..strglgth;
  begin
    lsp := nil;
    fvalu.ival := 0;
    if not (sy in constbegsys) then
    begin
      error(50);
      skip(fsys + constbegsys)
    end;
    if sy in constbegsys then
    begin
      if sy = stringconst then
      begin
        if lgth = 1 then
          lsp := charptr
        else
        begin
          New(lsp);
          pshstc(lsp);
          with lsp^ do
          begin
            aeltype := charptr;
            inxtype := nil;
            size := lgth * charsize;
            form := arrays;
            packing := True
          end
        end;
        fvalu := val;
        insymbol
      end
      else
      begin
        sign := none;
        if (sy = addop) and (op in [plus, minus]) then
        begin
          if op = plus then
            sign := pos
          else
            sign := neg;
          insymbol
        end;
        if sy = ident then
        begin
          searchid([konst], lcp);
          with lcp^ do
          begin
            lsp := idtype;
            fvalu := values
          end;
          if sign <> none then
            if lsp = intptr then
            begin
              if sign = neg then
                fvalu.ival := -fvalu.ival
            end
            else if lsp = realptr then
            begin
              if sign = neg then
              begin
                New(lvp);
                pshcst(lvp);
                lvp^.rval := nil;
                if strchr(fvalu.valp^.rval, 1) = '-' then
                  strchrass(lvp^.rval, 1, '+')
                else
                  strchrass(lvp^.rval, 1, '-');
                for i := 2 to digmax do
                  strchrass(lvp^.rval, i, strchr(fvalu.valp^.rval, i));
                fvalu.valp := lvp;
              end
            end
            else
              error(105);
          insymbol;
        end
        else if sy = intconst then
        begin
          if sign = neg then
            val.ival := -val.ival;
          lsp := intptr;
          fvalu := val;
          insymbol
        end
        else if sy = realconst then
        begin
          if sign = neg then
            strchrass(val.valp^.rval, 1, '-');
          lsp := realptr;
          fvalu := val;
          insymbol
        end
        else
        begin
          error(106);
          skip(fsys)
        end
      end;
      if not (sy in fsys) then
      begin
        error(6);
        skip(fsys)
      end
    end;
    fsp := lsp
  end { constant };

  function _string(fsp: stp): Boolean; forward;

  function comptypes(fsp1, fsp2: stp): Boolean;
    { decide whether structures pointed at by fsp1 and fsp2 are compatible }
  begin
    comptypes := False; { set default is False }
    { remove any subranges }
    fsp1 := basetype(fsp1);
    fsp2 := basetype(fsp2);
    { Check equal. Aliases of the same type will also be equal. }
    if fsp1 = fsp2 then
      comptypes := True
    else if (fsp1 <> nil) and (fsp2 <> nil) then
      if fsp1^.form = fsp2^.form then
        case fsp1^.form of
          scalar:
            ;
          { Subranges are compatible if either type is a subrange of the
            other, or if the base type is the same. }
          subrange:
            ; { done above }
          { Sets are compatible if they have the same base types and packed/
            unpacked status, or one of them is the empty set. The empty set
            is indicated by a nil base type, which is identical to a base
            type in error. Either way, we treat them as compatible.

            Set types created for set constants have a flag that disables
            packing matches. This is because set constants can be packed or
            unpacked by context. }
          power:
            comptypes := (comptypes(fsp1^.elset, fsp2^.elset) and
              ((fsp1^.packing = fsp2^.packing) or
              not fsp1^.matchpack or
              not fsp2^.matchpack)) or
            (fsp1^.elset = nil) or (fsp2^.elset = nil);
          { Arrays are compatible if they are string types and equal in size }
          arrays:
            comptypes := _string(fsp1) and _string(fsp2) and (fsp1^.size = fsp2^.size);
          { Pointers, must either be the same type or aliases of the same
            type, or one must be nil. The nil pointer is indicated by a nil
            base type, which is identical to a base type in error. Either
            way, we treat them as compatible. }
          pointer:
            comptypes := (fsp1^.eltype = nil) or (fsp2^.eltype = nil);
          { records and files must either be the same type or aliases of the
            same type }
          records:
            ;
          files:
        end
      else { fsp1^.form <> fsp2^.form }
        { subranges of a base type match the base type }
        if fsp1^.form = subrange then
          comptypes := fsp1^.rangetype = fsp2
        else if fsp2^.form = subrange then
          comptypes := fsp1 = fsp2^.rangetype
        else
          comptypes := False
      else
        comptypes := True { one of the types is in error }
  end { comptypes };

  { check structure is, or contains, a file }
  function filecomponent(fsp: stp): Boolean;
  var
    f: Boolean;
    { tour identifier tree }
    function filecomponentre(lcp: ctp): Boolean;
    var
      f: Boolean;
    begin
      f := False; { set not file by default }
      if lcp <> nil then
        with lcp^ do
        begin
          if filecomponent(idtype) then
            f := True;
          if filecomponentre(llink) then
            f := True;
          if filecomponentre(rlink) then
            f := True
        end;
      filecomponentre := f
    end { filecomponentre };
  begin
    f := False; { set not a file by default }
    if fsp <> nil then
      with fsp^ do
        case form of
          scalar:
            ;
          subrange:
            ;
          pointer:
            ;
          power:
            ;
          arrays:
            if filecomponent(aeltype) then
              f := True;
          records:
            if filecomponentre(fstfld) then
              f := True;
          files:
            f := True;
          tagfld:
            ;
          variant:
            ;
        end;
    filecomponent := f
  end { filecomponent };

  function _string;
  var
    fmin, fmax: Integer;
  begin
    _string := False;
    if fsp <> nil then
      if fsp^.form = arrays then
        if fsp^.packing then
        begin
          { if the index is nil, either the array is a string constant or the
            index type was in error. Either way, we call it a string }
          if fsp^.inxtype = nil then
            fmin := 1
          else
            getbounds(fsp^.inxtype, fmin, fmax);
          if comptypes(fsp^.aeltype, charptr) and (fmin = 1) then
            _string := True
        end
  end { _string };

  { resolve all pointer references in the forward list }
  procedure resolvep;
  var
    ids: idstr;
    lcp1, lcp2: ctp;
    mm, fe: Boolean;
  begin
    ids := id;
    fe := True;
    while fwptr <> nil do
    begin
      lcp1 := fwptr;
      fwptr := lcp1^.next;
      strassfv(id, lcp1^.name);
      searchidnenm([types], lcp2, mm);
      if lcp2 <> nil then
      begin
        lcp1^.idtype^.eltype := lcp2^.idtype;
        lcp2^.refer := True
      end
      else
      begin
        if fe then
        begin
          error(117);
          Writeln(Output)
        end;
        Write('*** undefined type-id forward reference: ');
        writev(Output, lcp1^.name, prtlln);
        Writeln;
        fe := False
      end;
      putnam(lcp1)
    end;
    id := ids
  end { resolvep };

  procedure typ(fsys: setofsys; var fsp: stp; var fsize: addrrange);
  var
    lsp, lsp1, lsp2: stp;
    oldtop: disprange;
    lcp: ctp;
    lsize, displ: addrrange;
    lmin, lmax: Integer;
    test: Boolean;
    ispacked: Boolean;

    procedure simpletype(fsys: setofsys; var fsp: stp; var fsize: addrrange);
    var
      lsp, lsp1: stp;
      lcp, lcp1: ctp;
      ttop: disprange;
      lcnt: Integer;
      lvalu: valu;
    begin
      fsize := 1;
      if not (sy in simptypebegsys) then
      begin
        error(1);
        skip(fsys + simptypebegsys)
      end;
      if sy in simptypebegsys then
      begin
        if sy = lparent then
        begin
          ttop := top; { decl. consts local to innermost block }
          while display[top].occur <> blck do
            top := top - 1;
          New(lsp);
          pshstc(lsp);
          with lsp^ do
          begin
            size := intsize;
            form := scalar;
            scalkind := declared;
            packing := False
          end;
          lcp1 := nil;
          lcnt := 0;
          repeat
            insymbol;
            if sy = ident then
            begin
              New(lcp);
              ininam(lcp);
              with lcp^ do
              begin
                strassvf(name, id);
                idtype := lsp;
                next := lcp1;
                values.ival := lcnt;
                klass := konst
              end;
              enterid(lcp);
              lcnt := lcnt + 1;
              lcp1 := lcp;
              insymbol
            end
            else
              error(2);
            if not (sy in fsys + [comma, rparent]) then
            begin
              error(6);
              skip(fsys + [comma, rparent])
            end
          until sy <> comma;
          lsp^.fconst := lcp1;
          top := ttop;
          if sy = rparent then
            insymbol
          else
            error(4);
          { resize for byte if needed }
          if isbyte(lsp) then
            lsp^.size := 1;
          fsize := lsp^.size
        end
        else
        begin
          if sy = ident then
          begin
            searchid([types, konst], lcp);
            insymbol;
            if lcp^.klass = konst then
            begin
              New(lsp);
              pshstc(lsp);
              with lsp^, lcp^ do
              begin
                form := subrange;
                rangetype := idtype;
                if _string(rangetype) then
                begin
                  error(148);
                  rangetype := nil
                end;
                min := values;
                size := intsize;
                packing := False
              end;
              if sy = range then
                insymbol
              else
                error(5);
              constant(fsys, lsp1, lvalu);
              lsp^.max := lvalu;
              if lsp^.rangetype <> lsp1 then
                error(107);
              if isbyte(lsp) then
                lsp^.size := 1
            end
            else
            begin
              lsp := lcp^.idtype;
              if lsp <> nil then
                fsize := lsp^.size
            end
          end { sy = ident }
          else
          begin
            New(lsp);
            pshstc(lsp);
            lsp^.form := subrange;
            lsp^.packing := False;
            constant(fsys + [range], lsp1, lvalu);
            if _string(lsp1) then
            begin
              error(148);
              lsp1 := nil
            end;
            with lsp^ do
            begin
              rangetype := lsp1;
              min := lvalu;
              size := intsize
            end;
            if sy = range then
              insymbol
            else
              error(5);
            constant(fsys, lsp1, lvalu);
            lsp^.max := lvalu;
            if lsp^.rangetype <> lsp1 then
              error(107);
            if isbyte(lsp) then
              lsp^.size := 1;
            fsize := lsp^.size
          end;
          if lsp <> nil then
            with lsp^ do
              if form = subrange then
                if rangetype <> nil then
                  if rangetype = realptr then
                    error(399)
                  else if min.ival > max.ival then
                    error(102)
        end;
        fsp := lsp;
        if not (sy in fsys) then
        begin
          error(6);
          skip(fsys)
        end
      end
      else
        fsp := nil
    end { simpletype };

    procedure fieldlist(fsys: setofsys; var frecvar: stp; vartyp: stp;
      varlab: ctp; lvl: Integer);
    var
      lcp, lcp1, nxt, nxt1: ctp;
      lsp, lsp1, lsp2, lsp3, lsp4: stp;
      minsize, maxsize, lsize: addrrange;
      lvalu: valu;
      test: Boolean;
      mm: Boolean;
    begin
      nxt1 := nil;
      lsp := nil;
      lcp := nil;
      if not (sy in (fsys + [ident, casesy])) then
      begin
        error(19);
        skip(fsys + [ident, casesy])
      end;
      while sy = ident do
      begin
        nxt := nxt1;
        repeat
          if sy = ident then
          begin
            New(lcp);
            ininam(lcp);
            with lcp^ do
            begin
              strassvf(name, id);
              idtype := nil;
              next := nxt;
              klass := field;
              varnt := vartyp;
              varlb := varlab;
              tagfield := False;
              taglvl := lvl;
              varsaddr := 0;
              varssize := 0
            end;
            nxt := lcp;
            enterid(lcp);
            insymbol
          end
          else
            error(2);
          if not (sy in [comma, colon]) then
          begin
            error(6);
            skip(fsys + [comma, colon, semicolon, casesy])
          end;
          test := sy <> comma;
          if not test then
            insymbol
        until test;
        if sy = colon then
          insymbol
        else
          error(5);
        typ(fsys + [casesy, semicolon], lsp, lsize);
        while nxt <> nxt1 do
          with nxt^ do
          begin
            alignu(lsp, displ);
            idtype := lsp;
            fldaddr := displ;
            nxt := next;
            displ := displ + lsize
          end;
        nxt1 := lcp;
        while sy = semicolon do
        begin
          insymbol;
          if not (sy in fsys + [ident, casesy, semicolon]) then
          begin
            error(19);
            skip(fsys + [ident, casesy])
          end
        end
      end;
      nxt := nil;
      while nxt1 <> nil do
        with nxt1^ do
        begin
          lcp := next;
          next := nxt;
          nxt := nxt1;
          nxt1 := lcp
        end;
      if sy = casesy then
      begin
        New(lsp);
        pshstc(lsp);
        with lsp^ do
        begin
          tagfieldp := nil;
          fstvar := nil;
          form := tagfld;
          packing := False
        end;
        frecvar := lsp;
        insymbol;
        if sy = ident then
        begin
          { find possible type first }
          searchidnenm([types], lcp1, mm);
          { now set up as field id }
          New(lcp);
          ininam(lcp);
          with lcp^ do
          begin
            strassvf(name, id);
            idtype := nil;
            klass := field;
            next := nil;
            fldaddr := displ;
            varnt := vartyp;
            varlb := varlab;
            tagfield := True;
            taglvl := lvl;
            varsaddr := 0;
            varssize := 0
          end;
          insymbol;
          if sy = colon then
          begin
            enterid(lcp);
            insymbol;
            if sy = ident then
            begin
              searchid([types], lcp1);
              insymbol
            end
            else
            begin
              error(2);
              skip(fsys + [ofsy, lparent]);
              lcp1 := nil
            end
          end
          else
          begin
            if lcp1 = nil then
            begin
              error(104);
              lcp1 := usclrptr
            end;
            { If type only (undiscriminated variant), kill the id. }
            if mm then
              error(103);
            putstrs(lcp^.name); { release name string }
            lcp^.name := nil { set no tagfield }
          end;
          if lcp1 <> nil then
          begin
            lsp1 := lcp1^.idtype;
            if lsp1 <> nil then
            begin
              alignu(lsp1, displ);
              lcp^.fldaddr := displ;
              { only allocate field if named or if undiscriminated
                tagfield checks are on }
              if (lcp^.name <> nil) or chkudtf then
                displ := displ + lsp1^.size;
              if (lsp1^.form <= subrange) or _string(lsp1) then
              begin
                if comptypes(realptr, lsp1) then
                  error(109)
                else if _string(lsp1) then
                  error(399);
                lcp^.idtype := lsp1;
                lsp^.tagfieldp := lcp;
              end
              else
                error(110);
            end
          end
        end
        else
        begin
          error(2);
          skip(fsys + [ofsy, lparent])
        end;
        lsp^.size := displ;
        if sy = ofsy then
          insymbol
        else
          error(8);
        lsp1 := nil;
        minsize := displ;
        maxsize := displ;
        repeat
          lsp2 := nil;
          if not (sy in fsys + [semicolon]) then
          begin
            repeat
              constant(fsys + [comma, colon, lparent], lsp3, lvalu);
              if lsp^.tagfieldp <> nil then
                if not comptypes(lsp^.tagfieldp^.idtype, lsp3) then
                  error(111);
              New(lsp3);
              pshstc(lsp3);
              with lsp3^ do
              begin
                nxtvar := lsp1;
                subvar := lsp2;
                varval := lvalu;
                caslst := lsp2;
                form := variant;
                packing := False
              end;
              lsp4 := lsp1;
              while lsp4 <> nil do
                with lsp4^ do
                begin
                  if varval.ival = lvalu.ival then
                    error(178);
                  lsp4 := nxtvar
                end;
              lsp1 := lsp3;
              lsp2 := lsp3;
              test := sy <> comma;
              if not test then
                insymbol
            until test;
            if sy = colon then
              insymbol
            else
              error(5);
            if sy = lparent then
              insymbol
            else
              error(9);
            alignu(nilptr, displ); { max align all variants }
            if lcp <> nil then
              lcp^.varsaddr := displ;
            fieldlist(fsys + [rparent, semicolon], lsp2, lsp3, lcp, lvl + 1);
            if displ > maxsize then
              maxsize := displ;
            if lcp <> nil then
              lcp^.varssize := maxsize - lcp^.varsaddr;
            while lsp3 <> nil do
            begin
              lsp4 := lsp3^.subvar;
              lsp3^.subvar := lsp2;
              lsp3^.size := displ;
              lsp3 := lsp4
            end;
            if sy = rparent then
            begin
              insymbol;
              if not (sy in fsys + [semicolon]) then
              begin
                error(6);
                skip(fsys + [semicolon])
              end
            end
            else
              error(4);
          end;
          test := sy <> semicolon;
          if not test then
          begin
            displ := minsize;
            insymbol
          end
        until test;
        displ := maxsize;
        lsp^.fstvar := lsp1;
      end
      else
        frecvar := nil
    end { fieldlist };

  begin { typ }
    if not (sy in typebegsys) then
    begin
      error(10);
      skip(fsys + typebegsys)
    end;
    if sy in typebegsys then
    begin
      if sy in simptypebegsys then
        simpletype(fsys, fsp, fsize)
      else
        if sy = arrow then
        begin
          New(lsp);
          pshstc(lsp);
          fsp := lsp;
          with lsp^ do
          begin
            eltype := nil;
            size := ptrsize;
            form := pointer;
            packing := False
          end;
          insymbol;
          if sy = ident then
          begin { forward reference everything }
            New(lcp);
            ininam(lcp);
            with lcp^ do
            begin
              strassvf(name, id);
              idtype := lsp;
              next := fwptr;
              klass := types
            end;
            fwptr := lcp;
            insymbol;
          end
          else
            error(2);
        end
        else
        begin
          ispacked := False; { set not packed by default }
          if sy = packedsy then
          begin
            insymbol;
            ispacked := True; { packed }
            if not (sy in typedels) then
            begin
              error(10);
              skip(fsys + typedels)
            end
          end;
          { array }if sy = arraysy then
          begin
            insymbol;
            if sy = lbrack then
              insymbol
            else
              error(11);
            lsp1 := nil;
            repeat
              New(lsp);
              pshstc(lsp);
              with lsp^ do
              begin
                aeltype := lsp1;
                inxtype := nil;
                form := arrays;
                packing := ispacked
              end;
              lsp1 := lsp;
              simpletype(fsys + [comma, rbrack, ofsy], lsp2, lsize);
              lsp1^.size := lsize;
              if lsp2 <> nil then
                if lsp2^.form <= subrange then
                begin
                  if lsp2 = realptr then
                  begin
                    error(109);
                    lsp2 := nil
                  end
                  else if lsp2 = intptr then
                  begin
                    error(149);
                    lsp2 := nil
                  end;
                  lsp^.inxtype := lsp2
                end
                else
                begin
                  error(113);
                  lsp2 := nil
                end;
              test := sy <> comma;
              if not test then
                insymbol
            until test;
            if sy = rbrack then
              insymbol
            else
              error(12);
            if sy = ofsy then
              insymbol
            else
              error(8);
            typ(fsys, lsp, lsize);
            repeat
              with lsp1^ do
              begin
                lsp2 := aeltype;
                aeltype := lsp;
                if inxtype <> nil then
                begin
                  getbounds(inxtype, lmin, lmax);
                  alignu(lsp, lsize);
                  lsize := lsize * (lmax - lmin + 1);
                  size := lsize
                end
              end;
              lsp := lsp1;
              lsp1 := lsp2
            until lsp1 = nil
          end
          else
            if sy = recordsy then
            begin
              insymbol;
              oldtop := top;
              if top < displimit then
              begin
                top := top + 1;
                with display[top] do
                begin
                  fname := nil;
                  flabel := nil;
                  fconst := nil;
                  fstruct := nil;
                  packing := False;
                  occur := rec
                end
              end
              else
                error(250);
              displ := 0;
              fieldlist(fsys - [semicolon] + [endsy], lsp1, nil, nil, 1);
              New(lsp);
              with lsp^ do
              begin
                fstfld := display[top].fname;
                display[top].fname := nil;
                recvar := lsp1;
                size := displ;
                form := records;
                packing := ispacked;
                recyc := display[top].fstruct;
                display[top].fstruct := nil
              end;
              putdsps(oldtop);
              top := oldtop;
              { register the record late because of the purge above }
              pshstc(lsp);
              if sy = endsy then
                insymbol
              else
                error(13)
            end
            else
              if sy = setsy then
              begin
                insymbol;
                if sy = ofsy then
                  insymbol
                else
                  error(8);
                simpletype(fsys, lsp1, lsize);
                if lsp1 <> nil then
                  if lsp1^.form > subrange then
                  begin
                    error(115);
                    lsp1 := nil
                  end
                  else if lsp1 = realptr then
                  begin
                    error(114);
                    lsp1 := nil
                  end
                  else if lsp1 = intptr then
                  begin
                    error(169);
                    lsp1 := nil
                  end
                  else
                  begin
                    getbounds(lsp1, lmin, lmax);
                    if (lmin < setlow) or (lmax > sethigh) then
                      error(169);
                  end;
                New(lsp);
                pshstc(lsp);
                with lsp^ do
                begin
                  elset := lsp1;
                  size := setsize;
                  form := power;
                  packing := ispacked;
                  matchpack := True
                end;
              end
              else
                if sy = filesy then
                begin
                  insymbol;
                  if sy = ofsy then
                    insymbol
                  else
                    error(8);
                  typ(fsys, lsp1, lsize);
                  if filecomponent(lsp1) then
                    error(190);
                  New(lsp);
                  pshstc(lsp);
                  with lsp^ do
                  begin
                    filtype := lsp1;
                    size := filesize + lsize;
                    form := files;
                    packing := ispacked
                  end
                end
                else
                  fsp := nil;
          fsp := lsp
        end;
      if not (sy in fsys) then
      begin
        error(6);
        skip(fsys)
      end
    end
    else
      fsp := nil;
    if fsp = nil then
      fsize := 1
    else
      fsize := fsp^.size
  end { typ };

  procedure labeldeclaration;
  var
    llp: lbp;
    test: Boolean;
  begin
    repeat
      if sy = intconst then
      begin
        searchlabel(llp, top); { search preexisting label }
        if llp <> nil then
          error(166) { multideclared label }
        else
          newlabel(llp);
        insymbol
      end
      else
        error(15);
      if not (sy in fsys + [comma, semicolon]) then
      begin
        error(6);
        skip(fsys + [comma, semicolon])
      end;
      test := sy <> comma;
      if not test then
        insymbol
    until test;
    if sy = semicolon then
      insymbol
    else
      error(14)
  end {  labeldeclaration  };

  procedure constdeclaration;
  var
    lcp: ctp;
    lsp: stp;
    lvalu: valu;
  begin
    if sy <> ident then
    begin
      error(2);
      skip(fsys + [ident])
    end;
    while sy = ident do
    begin
      New(lcp);
      ininam(lcp);
      with lcp^ do
      begin
        strassvf(name, id);
        idtype := nil;
        next := nil;
        klass := konst;
        refer := False
      end;
      insymbol;
      if (sy = relop) and (op = eqop) then
        insymbol
      else
        error(16);
      constant(fsys + [semicolon], lsp, lvalu);
      enterid(lcp);
      lcp^.idtype := lsp;
      lcp^.values := lvalu;
      if sy = semicolon then
      begin
        insymbol;
        if not (sy in fsys + [ident]) then
        begin
          error(6);
          skip(fsys + [ident])
        end
      end
      else
        error(14)
    end
  end { constdeclaration };

  procedure typedeclaration;
  var
    lcp: ctp;
    lsp: stp;
    lsize: addrrange;
  begin
    if sy <> ident then
    begin
      error(2);
      skip(fsys + [ident])
    end;
    while sy = ident do
    begin
      New(lcp);
      ininam(lcp);
      with lcp^ do
      begin
        strassvf(name, id);
        idtype := nil;
        klass := types;
        refer := False
      end;
      insymbol;
      if (sy = relop) and (op = eqop) then
        insymbol
      else
        error(16);
      typ(fsys + [semicolon], lsp, lsize);
      enterid(lcp);
      lcp^.idtype := lsp;
      if sy = semicolon then
      begin
        insymbol;
        if not (sy in fsys + [ident]) then
        begin
          error(6);
          skip(fsys + [ident])
        end
      end
      else
        error(14)
    end;
    resolvep
  end { typedeclaration };

  procedure vardeclaration;
  var
    lcp, nxt: ctp;
    lsp: stp;
    lsize: addrrange;
    test: Boolean;
  begin
    nxt := nil;
    repeat
      repeat
        if sy = ident then
        begin
          New(lcp);
          ininam(lcp);
          with lcp^ do
          begin
            strassvf(name, id);
            next := nxt;
            klass := vars;
            idtype := nil;
            vkind := actual;
            vlev := level;
            refer := False;
            threat := False;
            forcnt := 0
          end;
          enterid(lcp);
          nxt := lcp;
          insymbol;
        end
        else
          error(2);
        if not (sy in fsys + [comma, colon] + typedels) then
        begin
          error(6);
          skip(fsys + [comma, colon, semicolon] + typedels)
        end;
        test := sy <> comma;
        if not test then
          insymbol
      until test;
      if sy = colon then
        insymbol
      else
        error(5);
      typ(fsys + [semicolon] + typedels, lsp, lsize);
      while nxt <> nil do
        with nxt^ do
        begin
          idtype := lsp;
          { globals are alloc/increment, locals are decrement/alloc }
          if level <= 1 then
          begin
            alignu(lsp, gc);
            vaddr := gc;
            gc := gc + lsize
          end
          else
          begin
            lc := lc - lsize;
            alignd(lsp, lc);
            vaddr := lc
          end;
          nxt := next
        end;
      if sy = semicolon then
      begin
        insymbol;
        if not (sy in fsys + [ident]) then
        begin
          error(6);
          skip(fsys + [ident])
        end
      end
      else
        error(14)
    until (sy <> ident) and not (sy in typedels);
    resolvep
  end { vardeclaration };

  procedure procdeclaration(fsy: symbol);
  var
    oldlev: 0..maxlevel;
    lcp, lcp1: ctp;
    lsp: stp;
    forw: Boolean;
    oldtop: disprange;
    llc: stkoff;
    lbname: Integer; {markp: marktype;}

    procedure pushlvl(forw: Boolean; lcp: ctp);
    begin
      if level < maxlevel then
        level := level + 1
      else
        error(251);
      if top < displimit then
      begin
        top := top + 1;
        with display[top] do
        begin
          if forw then
            fname := lcp^.pflist
          else
            fname := nil;
          flabel := nil;
          fconst := nil;
          fstruct := nil;
          packing := False;
          occur := blck;
          bname := lcp
        end
      end
      else
        error(250);
    end { pushlvl };

    procedure parameterlist(fsy: setofsys; var fpar: ctp);
    var
      lcp, lcp1, lcp2, lcp3: ctp;
      lsp: stp;
      lkind: idkind;
      llc, lsize: addrrange;
      count: Integer;
      oldlev: 0..maxlevel;
      oldtop: disprange;
      lcs: addrrange;
      test: Boolean;
    begin
      lcp1 := nil;
      if not (sy in fsy + [lparent]) then
      begin
        error(7);
        skip(fsys + fsy + [lparent])
      end;
      if sy = lparent then
      begin
        if forw then
          error(119);
        insymbol;
        if not (sy in [ident, varsy, procsy, funcsy]) then
        begin
          error(7);
          skip(fsys + [ident, rparent])
        end;
        while sy in [ident, varsy, procsy, funcsy] do
        begin
          if sy = procsy then
          begin
            insymbol;
            lcp := nil;
            if sy = ident then
            begin
              New(lcp);
              ininam(lcp);
              lc := lc - ptrsize * 2; { mp and addr }
              alignd(parmptr, lc);
              with lcp^ do
              begin
                strassvf(name, id);
                idtype := nil;
                next := lcp1;
                pflev := level { beware of parameter procedures };
                klass := proc;
                pfdeckind := declared;
                pfkind := formal;
                pfaddr := lc;
                keep := True
              end;
              enterid(lcp);
              lcp1 := lcp;
              insymbol
            end
            else
              error(2);
            oldlev := level;
            oldtop := top;
            pushlvl(False, lcp);
            lcs := lc;
            parameterlist([semicolon, rparent], lcp2);
            lc := lcs;
            if lcp <> nil then
              lcp^.pflist := lcp2;
            if not (sy in fsys + [semicolon, rparent]) then
            begin
              error(7);
              skip(fsys + [semicolon, rparent])
            end;
            level := oldlev;
            putdsps(oldtop);
            top := oldtop
          end
          else
          begin
            if sy = funcsy then
            begin
              lcp2 := nil;
              insymbol;
              if sy = ident then
              begin
                New(lcp);
                ininam(lcp);
                lc := lc - ptrsize * 2; { mp and addr }
                alignd(parmptr, lc);
                with lcp^ do
                begin
                  strassvf(name, id);
                  idtype := nil;
                  next := lcp1;
                  pflev := level { beware param funcs };
                  klass := func;
                  pfdeckind := declared;
                  pfkind := formal;
                  pfaddr := lc;
                  keep := True
                end;
                enterid(lcp);
                lcp1 := lcp;
                insymbol;
              end
              else
                error(2);
              oldlev := level;
              oldtop := top;
              pushlvl(False, lcp);
              lcs := lc;
              parameterlist([colon, semicolon, rparent], lcp2);
              lc := lcs;
              if lcp <> nil then
                lcp^.pflist := lcp2;
              if not (sy in fsys + [colon]) then
              begin
                error(7);
                skip(fsys + [comma, semicolon, rparent])
              end;
              if sy = colon then
              begin
                insymbol;
                if sy = ident then
                begin
                  searchid([types], lcp2);
                  lsp := lcp2^.idtype;
                  lcp^.idtype := lsp;
                  if lsp <> nil then
                    if not (lsp^.form in [scalar, subrange, pointer]) then
                    begin
                      error(120)
                    end;
                  insymbol
                end
                else
                  error(2);
                if not (sy in fsys + [semicolon, rparent]) then
                begin
                  error(7);
                  skip(fsys + [semicolon, rparent])
                end
              end
              else
                error(5);
              level := oldlev;
              putdsps(oldtop);
              top := oldtop
            end
            else
            begin
              if sy = varsy then
              begin
                lkind := formal;
                insymbol
              end
              else
                lkind := actual;
              lcp2 := nil;
              count := 0;
              repeat
                if sy = ident then
                begin
                  New(lcp);
                  ininam(lcp);
                  with lcp^ do
                  begin
                    strassvf(name, id);
                    idtype := nil;
                    klass := vars;
                    vkind := lkind;
                    next := lcp2;
                    vlev := level;
                    keep := True;
                    refer := False;
                    threat := False;
                    forcnt := 0
                  end;
                  enterid(lcp);
                  lcp2 := lcp;
                  count := count + 1;
                  insymbol;
                end
                else
                  error(2);
                if not (sy in [comma, colon] + fsys) then
                begin
                  error(7);
                  skip(fsys + [comma, semicolon, rparent])
                end;
                test := sy <> comma;
                if not test then
                  insymbol
              until test;
              if sy = colon then
              begin
                insymbol;
                if sy = ident then
                begin
                  searchid([types], lcp);
                  lsp := lcp^.idtype;
                  lsize := ptrsize;
                  if lsp <> nil then
                    if lkind = actual then
                    begin
                      if lsp^.form <= power then
                        lsize := lsp^.size
                      else if lsp^.form = files then
                        error(121);
                      { type containing file not allowed either }
                      if filecomponent(lsp) then
                        error(121)
                    end;
                  alignu(parmptr, lsize);
                  lcp3 := lcp2;
                  lc := lc - count * lsize;
                  alignd(parmptr, lc);
                  llc := lc;
                  while lcp2 <> nil do
                  begin
                    lcp := lcp2;
                    with lcp2^ do
                    begin
                      idtype := lsp;
                      vaddr := llc;
                      llc := llc + lsize;
                    end;
                    lcp2 := lcp2^.next
                  end;
                  lcp^.next := lcp1;
                  lcp1 := lcp3;
                  insymbol
                end
                else
                begin
                  error(2);
                  { set any id list to tear down }
                  while lcp2 <> nil do
                  begin
                    lcp2^.keep := False;
                    lcp2 := lcp2^.next
                  end
                end;
                if not (sy in fsys + [semicolon, rparent]) then
                begin
                  error(7);
                  skip(fsys + [semicolon, rparent])
                end
              end
              else
              begin
                error(5);
                { set any id list to tear down }
                while lcp2 <> nil do
                begin
                  lcp2^.keep := False;
                  lcp2 := lcp2^.next
                end
              end
            end;
          end;
          if sy = semicolon then
          begin
            insymbol;
            if not (sy in fsys + [ident, varsy, procsy, funcsy]) then
            begin
              error(7);
              skip(fsys + [ident, rparent])
            end
          end
        end;
        if sy = rparent then
        begin
          insymbol;
          if not (sy in fsy + fsys) then
          begin
            error(6);
            skip(fsy + fsys)
          end
        end
        else
          error(4);
        lcp3 := nil;
        { reverse pointers and reserve local cells for copies of multiple
         values }
        while lcp1 <> nil do
          with lcp1^ do
          begin
            lcp2 := next;
            next := lcp3;
            if klass = vars then
              if idtype <> nil then
                if (vkind = actual) and (idtype^.form > power) then
                begin
                  lc := lc - idtype^.size;
                  alignd(idtype, lc);
                  vaddr := lc
                end;
            lcp3 := lcp1;
            lcp1 := lcp2
          end;
        fpar := lcp3
      end
      else
        fpar := nil
    end { parameterlist };

  begin { procdeclaration }
    llc := lc;
    lc := lcaftermarkstack;
    forw := False;
    if sy = ident then
    begin
      searchsection(display[top].fname, lcp); { decide whether forw. }
      if lcp <> nil then
      begin
        if lcp^.klass = proc then
          forw := lcp^.forwdecl and (fsy = procsy) and (lcp^.pfkind = actual)
        else if lcp^.klass = func then
          forw := lcp^.forwdecl and (fsy = funcsy) and (lcp^.pfkind = actual)
        else
          forw := False;
        if not forw then
          error(160)
      end;
      if not forw then
      begin
        if fsy = procsy then
          New(lcp)
        else
          New(lcp);
        ininam(lcp);
        with lcp^ do
        begin
          strassvf(name, id);
          idtype := nil;
          externl := False;
          pflev := level;
          genlabel(lbname);
          pfdeckind := declared;
          pfkind := actual;
          pfname := lbname;
          if fsy = procsy then
            klass := proc
          else
          begin
            klass := func;
            asgn := False
          end;
          refer := False
        end;
        enterid(lcp)
      end
      else
      begin
        lcp1 := lcp^.pflist;
        while lcp1 <> nil do
        begin
          with lcp1^ do
            if klass = vars then
              if idtype <> nil then
                if vaddr < lc then
                  lc := vaddr;
          lcp1 := lcp1^.next
        end
      end;
      insymbol
    end
    else
    begin
      error(2);
      if fsy = procsy then
        lcp := uprcptr
      else
        lcp := ufctptr
    end;
    oldlev := level;
    oldtop := top;
    pushlvl(forw, lcp);
    if fsy = procsy then
    begin
      parameterlist([semicolon], lcp1);
      if not forw then
        lcp^.pflist := lcp1
    end
    else
    begin
      parameterlist([semicolon, colon], lcp1);
      if not forw then
        lcp^.pflist := lcp1;
      if sy = colon then
      begin
        insymbol;
        if sy = ident then
        begin
          if forw then
            error(122);
          searchid([types], lcp1);
          lsp := lcp1^.idtype;
          lcp^.idtype := lsp;
          if lsp <> nil then
            if not (lsp^.form in [scalar, subrange, pointer]) then
            begin
              error(120);
              lcp^.idtype := nil
            end;
          insymbol
        end
        else
        begin
          error(2);
          skip(fsys + [semicolon])
        end
      end
      else if not forw then
        error(123)
    end;
    if sy = semicolon then
      insymbol
    else
      error(14);
    if (sy = ident) and strequri('forward  ', id) then
    begin
      if forw then
        error(161)
      else
        lcp^.forwdecl := True;
      insymbol;
      if sy = semicolon then
        insymbol
      else
        error(14);
      if not (sy in fsys) then
      begin
        error(6);
        skip(fsys)
      end
    end
    else
    begin
      lcp^.forwdecl := False;
      { mark(markp); }
      repeat
        block(fsys, semicolon, lcp);
        if sy = semicolon then
        begin
          if prtables then
            printtables(False);
          insymbol;
          if not (sy in [beginsy, procsy, funcsy]) then
          begin
            error(6);
            skip(fsys)
          end
        end
        else
          error(14)
      until (sy in [beginsy, procsy, funcsy]) or Eof(prd);
      if lcp^.klass = func then
        if lcp <> ufctptr then
          if not lcp^.asgn then
            error(193); { no function result assign }
      { release(markp); }{  return local entries on runtime heap  }
    end;
    level := oldlev;
    putdsps(oldtop);
    top := oldtop;
    lc := llc;
  end { procdeclaration };

  procedure body(fsys: setofsys);
  const
    cstoccmax = 4000;
    cixmax = 10000;
  type
    oprange = 0..maxins;
  var
    llcp: ctp;
    saveid: idstr;
    cstptr: array[1..cstoccmax] of csp;
    cstptrix: 0..cstoccmax;
    { allows referencing of noninteger constants by an index
     (instead of a pointer), which can be stored in the p2-field
     of the instruction record until writeout.
     --> procedure load, procedure writeout }
    entname, segsize, gblsize: Integer;
    stackbot, topnew, topmin: Integer;
    lcmin: stkoff;
    llc1: stkoff;
    lcp: ctp;
    llp: lbp;
    fp: extfilep;
    test: Boolean;
    printed: Boolean;

    { add statement level }
    procedure addlvl;
    begin
      stalvl := stalvl + 1
    end { addlvl };

    { remove statement level }
    procedure sublvl;
    var
      llp: lbp;
    begin
      stalvl := stalvl - 1;
      { traverse label list for current block and remove any label from
        active status whose statement block has closed }
      llp := display[top].flabel;
      while llp <> nil do
        with llp^ do
        begin
          if slevel > stalvl then
            bact := False;
          if refer and (minlvl > stalvl) then
            minlvl := stalvl;
          llp := nextlab { link next }
        end
    end { sublvl };

    procedure mesl(i: Integer);
    begin
      topnew := topnew + i;
      if topnew < topmin then
        topmin := topnew;
      if toterr = 0 then
        if topnew > 0 then
          error(500) { stack should never go positive }
    end { mesl };

    procedure mes(i: Integer);
    begin
      mesl(cdx[i])
    end { mes };

    procedure mest(i: Integer; fsp: stp);

      function mestn(fsp: stp): Integer;
      var
        ss: Integer;
      begin
        ss := 1;
        if fsp <> nil then
          with fsp^ do
            case form of
              scalar:
                if fsp = intptr then
                  ss := 1
                else if fsp = boolptr then
                  ss := 3
                else if fsp = charptr then
                  ss := 4
                else if scalkind = declared then
                  ss := 1
                else
                  ss := 2;
              subrange:
                ss := mestn(rangetype);
              pointer:
                ss := 5;
              power:
                ss := 6;
              records,
              arrays:
                ss := 7;
              files:
                ss := 5;
              tagfld, variant:
                error(500)
            end;
        mestn := ss
      end { mestn };

    begin
      if (cdx[i] < 1) and (cdx[i] > 6) then
        error(500);
      mesl(cdxs[cdx[i]][mestn(fsp)]);
    end { mest };

    procedure putic;
    begin
      if Mod2(ic, 10) = 0 then
        if prcode then
          Writeln(prr, 'i', ic: 5)
    end;

    procedure gen0(fop: oprange);
    begin
      putic;
      if prcode then
        Writeln(prr, string(mn[fop]): 4);
      ic := ic + 1;
      mes(fop)
    end { gen0 };

    procedure gen1(fop: oprange; fp2: Integer);
    var
      k, j: Integer;
      p: strvsp;
    begin
      putic;
      if prcode then
        Write(prr, string(mn[fop]): 4);
      if fop = 30 then
      begin
        if prcode then
          Writeln(prr, string(sna[fp2]): 12);
        mesl(pdx[fp2]);
      end
      else
      begin
        if fop = 38 then
        begin
          with cstptr[fp2]^ do
          begin
            p := sval;
            j := 1;
            if prcode then
              Write(prr, ' ', slgth: 4, ' ''');
            for k := 1 to lenpv(p) do
            begin
              if p^.str[j] = '''' then
                begin
                  if prcode then
                    Write(prr, '''''')
                end
              else
                begin
                  if prcode then
                    Write(prr, p^.str[j]: 1);
                end;
              j := j + 1;
              if j > varsqt then
              begin
                p := p^.next;
                j := 1
              end
            end
          end;
          if prcode then
            Writeln(prr, '''')
        end
        else if fop = 42 then
          begin
            if prcode then
              Writeln(prr, chr(fp2))
          end
        else if fop = 67 then
          begin
            if prcode then
              Writeln(prr, fp2: 4)
          end
        else
          begin
            if prcode then
              Writeln(prr, fp2: 12);
          end;
        if fop = 42 then
          mes(0)
        else
          mes(fop)
      end;
      ic := ic + 1
    end { gen1 };

    procedure gen2(fop: oprange; fp1, fp2: Integer);
    var
      k: Integer;
    begin
      putic;
      if prcode then
        Write(prr, string(mn[fop]): 4);
      case fop of
        45, 50, 54, 56, 74, 62, 63, 81, 82:
          begin
            if prcode then
              Writeln(prr, ' ', fp1: 3, fp2: 8);
            mes(fop)
          end;
        47, 48, 49, 52, 53, 55:
          begin
            if prcode then
              Write(prr, chr(fp1));
            if chr(fp1) = 'm' then
              begin
                if prcode then
                  Write(prr, ' ', fp2: 11);
              end;
            if prcode then
              Writeln(prr);
            case chr(fp1) of
              'i': mesl(cdxs[cdx[fop]][1]);
              'r': mesl(cdxs[cdx[fop]][2]);
              'b': mesl(cdxs[cdx[fop]][3]);
              'c': mesl(cdxs[cdx[fop]][4]);
              'a': mesl(cdxs[cdx[fop]][5]);
              's': mesl(cdxs[cdx[fop]][6]);
              'm': mesl(cdxs[cdx[fop]][7])
            end
          end;
        51:
          begin
            case fp1 of
              1:
                begin
                  if prcode then
                    Writeln(prr, 'i ', fp2: 1);
                  mesl(cdxs[cdx[fop]][1])
                end;
              2:
                begin
                  if prcode then
                    Write(prr, 'r ');
                  with cstptr[fp2]^ do
                    if prcode then
                      writev(prr, rval, lenpv(rval));
                  if prcode then
                    Writeln(prr);
                  mesl(cdxs[cdx[fop]][2]);
                end;
              3:
                begin
                  if prcode then
                    Writeln(prr, 'b ', fp2: 1);
                  mesl(cdxs[cdx[fop]][3])
                end;
              4:
                begin
                  if prcode then
                    Writeln(prr, 'n');
                  mesl(-ptrsize)
                end;
              6:
                begin
                  if chartp[chr(fp2)] = illegal then
                    { Output illegal characters as numbers }
                    begin
                      if prcode then
                        Writeln(prr, 'c  ': 3, fp2: 1)
                    end
                  else
                    begin
                      if prcode then
                        Writeln(prr, 'c ''': 3, chr(fp2), '''');
                    end;
                  mesl(cdxs[cdx[fop]][4])
                end;
              5:
                begin
                  if prcode then
                    Write(prr, 's(');
                  with cstptr[fp2]^ do
                    for k := setlow to sethigh do
                      {  increased for testing [sam]  }
                      if k in pval then
                        begin
                          if prcode then
                            Write(prr, k: 7 { 3 });
                        end;
                  if prcode then
                    Writeln(prr, ')');
                  mesl(cdxs[cdx[fop]][6])
                end
            end
          end
      end;
      ic := ic + 1
    end { gen2 };

    procedure gentypindicator(fsp: stp);
    begin
      if fsp <> nil then
        with fsp^ do
          case form of
            scalar:
              if fsp = intptr then
                begin
                  if prcode then
                    Write(prr, 'i')
                end
              else if fsp = boolptr then
                begin
                  if prcode then
                    Write(prr, 'b')
                end
              else if fsp = charptr then
                begin
                  if prcode then
                    Write(prr, 'c')
                end
              else if scalkind = declared then
              begin
                if fsp^.size = 1 then
                  begin
                    if prcode then
                      Write(prr, 'x')
                  end
                else
                  begin
                    if prcode then
                      Write(prr, 'i')
                  end;
              end
              else
                begin
                  if prcode then
                    Write(prr, 'r');
                end;
            subrange:
              if fsp^.size = 1 then
                begin
                  if prcode then
                    Write(prr, 'x')
                end
              else
                gentypindicator(rangetype);
            pointer:
              if prcode then
                Write(prr, 'a');
            power:
              if prcode then
                Write(prr, 's');
            records,
            arrays:
              if prcode then
                Write(prr, 'm');
            files:
              if prcode then
                Write(prr, 'a');
            tagfld,
            variant:
              error(500)
          end
    end { gentypindicator };

    procedure gen0t(fop: oprange; fsp: stp);
    begin
      putic;
      if prcode then
        Write(prr, string(mn[fop]): 4);
      gentypindicator(fsp);
      if prcode then
        Writeln(prr);
      ic := ic + 1;
      mest(fop, fsp)
    end { gen0t };

    procedure gen1t(fop: oprange; fp2: Integer; fsp: stp);
    begin
      putic;
      if prcode then
        Write(prr, string(mn[fop]): 4);
      gentypindicator(fsp);
      if prcode then
        Writeln(prr, ' ', fp2: 11);
      ic := ic + 1;
      mest(fop, fsp)
    end { gen1t };

    procedure gen2t(fop: oprange; fp1, fp2: Integer; fsp: stp);
    begin
      putic;
      if prcode then
        Write(prr, string(mn[fop]): 4);
      gentypindicator(fsp);
      if prcode then
        Writeln(prr, ' ', fp1: 3 + 5 * Ord(Abs(fp1) > 99), fp2: 11);
      ic := ic + 1;
      mest(fop, fsp)
    end { gen2t };

    procedure load;
    begin
      with gattr do
        if typtr <> nil then
        begin
          case kind of
            cst:
              if (typtr^.form = scalar) and (typtr <> realptr) then
                if typtr = boolptr then
                  gen2(51 { ldc }, 3, cval.ival)
                else if typtr = charptr then
                  gen2(51 { ldc }, 6, cval.ival)
                else
                  gen2(51 { ldc }, 1, cval.ival)
              else if typtr = nilptr then
                gen2(51 { ldc }, 4, 0)
              else if cstptrix >= cstoccmax then
                error(254)
              else
              begin
                cstptrix := cstptrix + 1;
                cstptr[cstptrix] := cval.valp;
                if typtr = realptr then
                  gen2(51 { ldc }, 2, cstptrix)
                else
                  gen2(51 { ldc }, 5, cstptrix)
              end;
            varbl:
              case access of
                drct:
                  if vlevel <= 1 then
                    gen1t(39 { ldo }, dplmt, typtr)
                  else
                    gen2t(54 { lod }, level - vlevel, dplmt, typtr);
                indrct:
                  gen1t(35 { ind }, idplmt, typtr);
                inxd:
                  error(400)
              end;
            expr:
          end;
          kind := expr;
          { operand is loaded, and subranges are now normalized to their
            base type }
          typtr := basetype(typtr)
        end
    end { load };

    procedure store(var fattr: attr);
    begin
      with fattr do
        if typtr <> nil then
          case access of
            drct:
              if vlevel <= 1 then
                gen1t(43 { sro }, dplmt, typtr)
              else
                gen2t(56 { str }, level - vlevel, dplmt, typtr);
            indrct:
              if idplmt <> 0 then
                error(400)
              else
                gen0t(26 { sto }, typtr);
            inxd:
              error(400)
          end
    end { store };

    procedure loadaddress;
    begin
      with gattr do
        if typtr <> nil then
        begin
          case kind of
            cst:
              if _string(typtr) then
                if cstptrix >= cstoccmax then
                  error(254)
                else
                begin
                  cstptrix := cstptrix + 1;
                  cstptr[cstptrix] := cval.valp;
                  gen1(38 { lca }, cstptrix)
                end
              else
                error(400);
            varbl:
              case access of
                drct:
                  if vlevel <= 1 then
                    gen1(37 { lao }, dplmt)
                  else
                    gen2(50 { lda }, level - vlevel, dplmt);
                indrct:
                  if idplmt <> 0 then
                    gen1t(34 { inc }, idplmt, nilptr);
                inxd:
                  error(400)
              end;
            expr:
              error(400)
          end;
          kind := varbl;
          access := indrct;
          idplmt := 0;
          packing := False
        end
    end { loadaddress };

    procedure genfjp(faddr: Integer);
    begin
      load;
      if gattr.typtr <> nil then
        if gattr.typtr <> boolptr then
          error(144);
      putic;
      if prcode then
        Writeln(prr, string(mn[33]): 4, ' l': 8, faddr: 4);
      ic := ic + 1;
      mes(33)
    end { genfjp };

    procedure genujpxjp(fop: oprange; fp2: Integer);
    begin
      putic;
      if prcode then
        Writeln(prr, string(mn[fop]): 4, ' l': 8, fp2: 4);
      ic := ic + 1;
      mes(fop)
    end { genujpxjp };

    procedure genipj(fop: oprange; fp1, fp2: Integer);
    begin
      putic;
      if prcode then
        Writeln(prr, string(mn[fop]): 4, fp1: 4, ' l': 8, fp2: 4);
      ic := ic + 1;
      mes(fop)
    end { genujpxjp };

    procedure gencupent(fop: oprange; fp1, fp2: Integer);
    begin
      putic;
      if fop = 32 then
      begin { create ents or ente instructions }
        if fp1 = 1 then
          begin
            if prcode then
              Writeln(prr, string(mn[fop]): 4, 's', 'l': 8, fp2: 4)
          end
        else
          begin
            if prcode then
              Writeln(prr, string(mn[fop]): 4, 'e', 'l': 8, fp2: 4);
          end;
        mes(fop)
      end
      else
      begin
        if prcode then
          Writeln(prr, string(mn[fop]): 4, fp1: 4, 'l': 4, fp2: 4);
        mesl(fp1)
      end;
      ic := ic + 1
    end { gencupent };

    procedure genlpa(fp1, fp2: Integer);
    begin
      putic;
      if prcode then
        Writeln(prr, string(mn[68]): 4, fp2: 4, 'l': 4, fp1: 4);
      ic := ic + 1;
      mes(68)
    end { genlpa };

    procedure checkbnds(fsp: stp);
    var
      lmin, lmax: Integer;
      fsp2: stp;
    begin
      { if set use the base type for the check }
      fsp2 := fsp;
      if fsp^.form = power then
        fsp := fsp^.elset;
      if fsp <> nil then
        if fsp <> intptr then
          if fsp <> realptr then
            if fsp^.form <= subrange then
            begin
              getbounds(fsp, lmin, lmax);
              gen2t(45 { chk }, lmin, lmax, fsp2)
            end
    end { checkbnds };

    procedure putlabel(labname: Integer);
    begin
      if prcode then
        Writeln(prr, 'l', labname: 4)
    end { putlabel };

    procedure statement(fsys: setofsys);
    var
      lcp: ctp;
      llp: lbp;

      procedure expression(fsys: setofsys; threaten: Boolean); forward;

      function taggedrec(fsp: stp): Boolean;
      var
        b: Boolean;
      begin
        b := False;
        if fsp <> nil then
          if fsp^.form = tagfld then
            b := True
          else if fsp^.form = records then
            if fsp^.recvar <> nil then
              b := fsp^.recvar^.form = tagfld;
        taggedrec := b
      end { taggedrec };

      procedure selector(fsys: setofsys; fcp: ctp);
      var
        lattr: attr;
        lcp: ctp;
        lsize: addrrange;
        lmin, lmax: Integer;
        id: stp;
        function schblk(fcp: ctp): Boolean;
        var
          i: disprange;
          f: Boolean;
        begin
          f := False;
          for i := level downto 2 do
            if display[i].bname = fcp then
              f := True;
          schblk := f
        end { schblk };
        procedure checkvrnt(lcp: ctp);
        var
          vp: stp;
          vl: ctp;
          gattrs: attr;
        begin
          if chkvar then
          begin
            if lcp^.klass = field then
            begin
              vp := lcp^.varnt;
              vl := lcp^.varlb;
              if vp <> nil then
                if vl^.name <> nil then
                begin { is a variant }
                  gattrs := gattr;
                  with gattr, vl^ do
                  begin
                    typtr := idtype;
                    case access of
                      drct:
                        dplmt := dplmt + fldaddr;
                      indrct:
                        begin
                          idplmt := idplmt + fldaddr;
                          gen0t(76 { dup }, nilptr)
                        end;
                      inxd:
                        error(400)
                    end;
                    load;
                    gen0(78 { cks });
                    while vp <> nil do
                    begin
                      gen1t(75 { ckv }, vp^.varval.ival, basetype(idtype));
                      vp := vp^.caslst
                    end;
                    gen0(77 { cke });
                  end;
                  gattr := gattrs
                end
            end
          end
        end { checkvrnt };
      begin
        with fcp^, gattr do
        begin
          typtr := idtype;
          kind := varbl;
          packing := False;
          packcom := False;
          tagfield := False;
          ptrref := False;
          case klass of
            vars:
              begin
                if typtr <> nil then
                  packing := typtr^.packing;
                if vkind = actual then
                begin
                  access := drct;
                  vlevel := vlev;
                  dplmt := vaddr
                end
                else
                begin
                  gen2t(54 { lod }, level - vlev, vaddr, nilptr);
                  access := indrct;
                  idplmt := 0
                end;
              end;
            field:
              with display[disx] do
              begin
                gattr.packcom := display[disx].packing;
                if typtr <> nil then
                  gattr.packing := display[disx].packing or typtr^.packing;
                gattr.ptrref := display[disx].ptrref;
                gattr.tagfield := fcp^.tagfield;
                gattr.taglvl := fcp^.taglvl;
                gattr.varnt := fcp^.varnt;
                if gattr.tagfield then
                  gattr.vartagoff := fcp^.varsaddr - fldaddr;
                gattr.varssize := fcp^.varssize;
                if occur = crec then
                begin
                  access := drct;
                  vlevel := clev;
                  dplmt := cdspl + fldaddr
                end
                else if occur = vrec then
                begin
                  { override to local for with statement }
                  gen2t(54 { lod }, 0, vdspl, nilptr);
                  access := indrct;
                  idplmt := fldaddr
                end
                else
                begin
                  if level = 1 then
                    gen1t(39 { ldo }, vdspl, nilptr)
                  else
                    gen2t(54 { lod }, 0, vdspl, nilptr);
                  access := indrct;
                  idplmt := fldaddr
                end
              end;
            func:
              if pfdeckind = standard then
              begin
                error(150);
                typtr := nil
              end
              else
              begin
                if pfkind = formal then
                  error(151)
                else if not schblk(fcp) then
                  error(192);
                begin
                  access := drct;
                  vlevel := pflev + 1;
                  { determine size of FR. This is a bit of a hack
                    against the fact that int/ptr results fit in
                    the upper half of the FR. }
                  id := basetype(fcp^.idtype);
                  lsize := maxresult;
                  if id <> nil then
                    lsize := id^.size;
                  if lsize < maxresult then
                    { impl. relat. addr. of fct. result }
                    dplmt := markfv + trunc(maxresult / 2)
                  else
                    dplmt := markfv { impl. relat. addr. of fct. result }
                end
              end
          end
        end;
        if not (sy in selectsys + fsys) then
        begin
          error(59);
          skip(selectsys + fsys)
        end;
        while sy in selectsys do
        begin
          { [ }if sy = lbrack then
          begin
            gattr.ptrref := False;
            repeat
              lattr := gattr;
              with lattr do
                if typtr <> nil then
                begin
                  if typtr^.form <> arrays then
                  begin
                    error(138);
                    typtr := nil
                  end
                end;
              loadaddress;
              insymbol;
              expression(fsys + [comma, rbrack], False);
              load;
              if gattr.typtr <> nil then
                if gattr.typtr^.form <> scalar then
                  error(113)
                else if not comptypes(gattr.typtr, intptr) then
                  gen0t(58 { Ord }, gattr.typtr);
              if lattr.typtr <> nil then
                with lattr.typtr^ do
                begin
                  if comptypes(inxtype, gattr.typtr) then
                  begin
                    if inxtype <> nil then
                    begin
                      getbounds(inxtype, lmin, lmax);
                      if debug then
                        gen2t(45 { chk }, lmin, lmax, intptr);
                      if lmin > 0 then
                        gen1t(31 { dec }, lmin, intptr)
                      else if lmin < 0 then
                        gen1t(34 { inc }, -lmin, intptr);
                      { or simply gen1(31,lmin) }
                    end
                  end
                  else
                    error(139);
                  with gattr do
                  begin
                    typtr := aeltype;
                    kind := varbl;
                    access := indrct;
                    idplmt := 0;
                    packing := False;
                    packcom := False;
                    tagfield := False;
                    ptrref := False
                  end;
                  if gattr.typtr <> nil then
                  begin
                    gattr.packcom := lattr.packing;
                    gattr.packing :=
                      lattr.packing or gattr.typtr^.packing;
                    lsize := gattr.typtr^.size;
                    gen1(36 { ixa }, lsize)
                  end
                end
            until sy <> comma;
            if sy = rbrack then
              insymbol
            else
              error(12)
          end { if sy = lbrack }
          else
            if sy = period then
            begin
              with gattr do
              begin
                if typtr <> nil then
                begin
                  if typtr^.form <> records then
                  begin
                    error(140);
                    typtr := nil
                  end
                end;
                insymbol;
                if sy = ident then
                begin
                  if typtr <> nil then
                  begin
                    searchsection(typtr^.fstfld, lcp);
                    if lcp = nil then
                    begin
                      error(152);
                      typtr := nil
                    end
                    else
                      with lcp^ do
                      begin
                        checkvrnt(lcp);
                        typtr := idtype;
                        gattr.packcom := gattr.packing;
                        if typtr <> nil then
                          gattr.packing :=
                            gattr.packing or typtr^.packing;
                        gattr.tagfield := lcp^.tagfield;
                        gattr.taglvl := lcp^.taglvl;
                        gattr.varnt := lcp^.varnt;
                        if gattr.tagfield then
                          gattr.vartagoff := lcp^.varsaddr - fldaddr;
                        gattr.varssize := lcp^.varssize;
                        case access of
                          drct:
                            dplmt := dplmt + fldaddr;
                          indrct:
                            idplmt := idplmt + fldaddr;
                          inxd:
                            error(400)
                        end
                      end
                  end;
                  insymbol
                end { sy = ident }
                else
                  error(2)
              end { with gattr }
            end { if sy = period }
            else
              { ^ }
            begin
              if gattr.typtr <> nil then
                with gattr, typtr^ do
                  if form = pointer then
                  begin
                    load;
                    typtr := eltype;
                    if debug then
                    begin
                      if taggedrec(eltype) then
                        gen2t(80 { ckl }, 1, maxaddr, nilptr)
                      else
                        gen2t(45 { chk }, 1, maxaddr, nilptr);
                    end;
                    with gattr do
                    begin
                      kind := varbl;
                      access := indrct;
                      idplmt := 0;
                      packing := False;
                      packcom := False;
                      tagfield := False;
                      ptrref := True;
                    end
                  end
                  else if form = files then
                  begin
                    loadaddress;
                    { generate buffer validate for file }
                    if typtr = textptr then
                      gen1(30 { csp }, 46 { fbv })
                    else
                    begin
                      gen2(51 { ldc }, 1, filtype^.size);
                      gen1(30 { csp }, 47 { fvb })
                    end;
                    { index buffer }
                    gen1t(34 { inc }, fileidsize, gattr.typtr);
                    typtr := filtype;
                  end
                  else
                    error(141);
              insymbol
            end;
          if not (sy in fsys + selectsys) then
          begin
            error(6);
            skip(fsys + selectsys)
          end
        end
      end { selector };

      procedure call(fsys: setofsys; fcp: ctp);
      var
        lkey: 1..18;

        procedure variable(fsys: setofsys; threaten: Boolean);
        var
          lcp: ctp;
        begin
          if sy = ident then
          begin
            searchid([vars, field], lcp);
            insymbol
          end
          else
          begin
            error(2);
            lcp := uvarptr
          end;
          if threaten and (lcp^.klass = vars) then
            with lcp^ do
            begin
              if vlev < level then
                threat := True;
              if forcnt > 0 then
                error(195);
            end;
          selector(fsys, lcp)
        end { variable };

        procedure getputresetrewriteprocedure;
        begin
          variable(fsys + [rparent], False);
          loadaddress;
          if gattr.typtr <> nil then
            if gattr.typtr^.form <> files then
              error(116);
          if lkey <= 2 then
          begin
            if gattr.typtr = textptr then
              gen1(30 { csp }, lkey { get,put })
            else
            begin
              if gattr.typtr <> nil then
                gen2(51 { ldc }, 1, gattr.typtr^.filtype^.size);
              if lkey = 1 then
                gen1(30 { csp }, 38 { gbf })
              else
                gen1(30 { csp }, 39 { pbf })
            end
          end
          else if gattr.typtr = textptr then
          begin
            if lkey = 3 then
              gen1(30 { csp }, 25 { reset })
            else
              gen1(30 { csp }, 26 { rewrite })
          end
          else
          begin
            if lkey = 3 then
              gen1(30 { csp }, 36 { reset })
            else
              gen1(30 { csp }, 37 { rewrite })
          end
        end { getputresetrewrite };

        procedure pageprocedure;
        begin
          if sy = lparent then
          begin
            insymbol;
            variable(fsys + [rparent], False);
            loadaddress;
            if gattr.typtr <> nil then
              if gattr.typtr <> textptr then
                error(116);
            if sy = rparent then
              insymbol
            else
              error(4)
          end
          else
          begin
            if not outputhdf then
              error(176);
            gen1(37 { lao }, outputptr^.vaddr);
          end;
          gen1(30 { csp }, 24 { page })
        end { pageprocedure };

        procedure readprocedure;
        var
          lsp: stp;
          txt: Boolean; { is a text file }
          deffil: Boolean; { default file was loaded }
          test: Boolean;
          lmin, lmax: Integer;
        begin
          txt := True;
          deffil := True;
          if sy = lparent then
          begin
            insymbol;
            variable(fsys + [comma, rparent], True);
            lsp := gattr.typtr;
            test := False;
            if lsp <> nil then
              if lsp^.form = files then
                with gattr, lsp^ do
                begin
                  txt := lsp = textptr;
                  if not txt and (lkey = 11) then
                    error(116);
                  loadaddress;
                  deffil := False;
                  if sy = rparent then
                  begin
                    if lkey = 5 then
                      error(116);
                    test := True
                  end
                  else if sy <> comma then
                  begin
                    error(116);
                    skip(fsys + [comma, rparent])
                  end;
                  if sy = comma then
                  begin
                    insymbol;
                    variable(fsys + [comma, rparent], True)
                  end
                  else
                    test := True
                end
              else if not inputhdf then
                error(175);
            if not test then
              repeat
                loadaddress;
                if deffil then
                begin
                  { file was not loaded, we load and swap so that it ends up
                    on the bottom.}
                  gen1(37 { lao }, inputptr^.vaddr);
                  gen1(72 { swp }, ptrsize); { note 2nd is always pointer }
                  deffil := False
                end;
                if txt then
                begin
                  if gattr.typtr <> nil then
                    if gattr.typtr^.form <= subrange then
                      if comptypes(intptr, gattr.typtr) then
                      begin
                        if debug then
                        begin
                          getbounds(gattr.typtr, lmin, lmax);
                          gen1t(51 { ldc }, lmin, basetype(gattr.typtr));
                          gen1t(51 { ldc }, lmax, basetype(gattr.typtr));
                          gen1(30 { csp }, 40 { rib })
                        end
                        else
                          gen1(30 { csp }, 3 { rdi })
                      end
                      else if comptypes(realptr, gattr.typtr) then
                        gen1(30 { csp }, 4 { rdr })
                      else if comptypes(charptr, gattr.typtr) then
                      begin
                        if debug then
                        begin
                          getbounds(gattr.typtr, lmin, lmax);
                          gen2(51 { ldc }, 6, lmin);
                          gen2(51 { ldc }, 6, lmax);
                          gen1(30 { csp }, 41 { rcb })
                        end
                        else
                          gen1(30 { csp }, 5 { rdc })
                      end
                      else
                        error(399)
                    else
                      error(116);
                end
                else
                begin { binary file }
                  if not comptypes(gattr.typtr, lsp^.filtype) then
                    error(129);
                  gen2(51 { ldc }, 1, lsp^.filtype^.size);
                  gen1(30 { csp }, 35 { rbf })
                end;
                test := sy <> comma;
                if not test then
                begin
                  insymbol;
                  variable(fsys + [comma, rparent], True)
                end
              until test;
            if sy = rparent then
              insymbol
            else
              error(4)
          end
          else
          begin
            if not inputhdf then
              error(175);
            if lkey = 5 then
              error(116);
            gen1(37 { lao }, inputptr^.vaddr);
          end;
          if lkey = 11 then
            gen1(30 { csp }, 21 { rln });
          { remove the file pointer from stack }
          gen1(71 { dmp }, ptrsize);
        end { readprocedure };

        procedure writeprocedure;
        var
          lsp, lsp1: stp;
          default, default1: Boolean;
          llkey: 1..15;
          len: addrrange;
          txt: Boolean; { is a text file }
          byt: Boolean; { is a byte file }
          deffil: Boolean; { default file was loaded }
          test: Boolean;
        begin
          llkey := lkey;
          txt := True;
          deffil := True;
          byt := False;
          lsp1 := nil;
          if sy = lparent then
          begin
            insymbol;
            expression(fsys + [comma, colon, rparent], False);
            lsp := gattr.typtr;
            test := False;
            if lsp <> nil then
              if lsp^.form = files then
                with gattr, lsp^ do
                begin
                  lsp1 := lsp;
                  txt := lsp = textptr;
                  if not txt then
                  begin
                    if lkey = 12 then
                      error(116);
                    byt := isbyte(lsp^.filtype)
                  end;
                  loadaddress;
                  deffil := False;
                  if sy = rparent then
                  begin
                    if llkey = 6 then
                      error(116);
                    test := True
                  end
                  else if sy <> comma then
                  begin
                    error(116);
                    skip(fsys + [comma, rparent])
                  end;
                  if sy = comma then
                  begin
                    insymbol;
                    expression(fsys + [comma, colon, rparent], False)
                  end
                  else
                    test := True
                end
              else if not outputhdf then
                error(176);
            if not test then
              repeat
                lsp := gattr.typtr;
                if lsp <> nil then
                  if lsp^.form <= subrange then
                    load
                  else
                    loadaddress;
                lsp := basetype(lsp); { remove any subrange }
                if deffil then
                begin
                  { file was not loaded, we load and swap so that it ends up
                    on the bottom.}
                  gen1(37 { lao }, outputptr^.vaddr);
                  if lsp <> nil then
                    if lsp^.form <= subrange then
                    begin
                      if lsp^.size < stackelsize then
                        gen1(72 { swp }, stackelsize)
                          { size of 2nd is minimum stack }
                      else
                        gen1(72 { swp }, lsp^.size) { size of 2nd is operand }
                    end
                    else
                      gen1(72 { swp }, ptrsize); { size of 2nd is pointer }
                  deffil := False
                end;
                if txt then
                begin
                  if sy = colon then
                  begin
                    insymbol;
                    expression(fsys + [comma, colon, rparent], False);
                    if gattr.typtr <> nil then
                      if gattr.typtr <> intptr then
                        error(116);
                    load;
                    default := False
                  end
                  else
                    default := True;
                  if sy = colon then
                  begin
                    insymbol;
                    expression(fsys + [comma, rparent], False);
                    if gattr.typtr <> nil then
                      if gattr.typtr <> intptr then
                        error(116);
                    if lsp <> realptr then
                      error(124);
                    load;
                    default1 := False
                  end
                  else
                    default1 := True;
                  if lsp = intptr then
                  begin
                    if default then
                      gen2(51 { ldc }, 1, intdeff);
                    gen1(30 { csp }, 6 { wri })
                  end
                  else if lsp = realptr then
                  begin
                    if default1 then
                    begin
                      if default then
                        gen2(51 { ldc }, 1, reldeff);
                      gen1(30 { csp }, 8 { wrr })
                    end
                    else
                    begin
                      if default then
                        gen2(51 { ldc }, 1, reldeff);
                      gen1(30 { csp }, 28 { wrf })
                    end
                  end
                  else if lsp = charptr then
                  begin
                    if default then
                      gen2(51 { ldc }, 1, chrdeff);
                    gen1(30 { csp }, 9 { wrc })
                  end
                  else if lsp = boolptr then
                  begin
                    if default then
                      gen2(51 { ldc }, 1, boldeff);
                    gen1(30 { csp }, 27 { wrb })
                  end
                  else if lsp <> nil then
                  begin
                    if lsp^.form = scalar then
                      error(399)
                    else if _string(lsp) then
                    begin
                      len := lsp^.size div charmax;
                      if default then
                        gen2(51 { ldc }, 1, len);
                      gen2(51 { ldc }, 1, len);
                      gen1(30 { csp }, 10 { wrs })
                    end
                    else
                      error(116)
                  end
                end
                else
                begin { binary file }
                  if not comptypes(lsp1^.filtype, lsp) then
                    error(129);
                  if lsp <> nil then
                    if (lsp = intptr) and not byt then
                      gen1(30 { csp }, 31 { wbi })
                    else if lsp = realptr then
                      gen1(30 { csp }, 32 { wbr })
                    else if lsp = charptr then
                      gen1(30 { csp }, 33 { wbc })
                    else if lsp = boolptr then
                      gen1(30 { csp }, 34 { wbb })
                    else if lsp^.form <= subrange then
                    begin
                      if byt then
                        gen1(30 { csp }, 48 { wbx })
                      else
                        gen1(30 { csp }, 31 { wbi })
                    end
                    else
                    begin
                      gen2(51 { ldc }, 1, lsp1^.filtype^.size);
                      gen1(30 { csp }, 30 { wbf })
                    end
                end;
                test := sy <> comma;
                if not test then
                begin
                  insymbol;
                  expression(fsys + [comma, colon, rparent], False)
                end
              until test;
            if sy = rparent then
              insymbol
            else
              error(4)
          end
          else
          begin
            if not outputhdf then
              error(176);
            if lkey = 6 then
              error(116);
            gen1(37 { lao }, outputptr^.vaddr);
          end;
          if llkey = 12 then { Writeln }
            gen1(30 { csp }, 22 { wln });
          { remove the file pointer from stack }
          gen1(71 { dmp }, ptrsize);
        end { writeprocedure };

        procedure packprocedure;
        var
          lsp, lsp1: stp;
          lb, bs: Integer;
          lattr: attr;
        begin
          variable(fsys + [comma, rparent], False);
          loadaddress;
          lsp := nil;
          lsp1 := nil;
          lb := 1;
          bs := 1;
          lattr := gattr;
          if gattr.typtr <> nil then
            with gattr.typtr^ do
              if form = arrays then
              begin
                lsp := inxtype;
                lsp1 := aeltype;
                if (inxtype = charptr) or (inxtype = boolptr) then
                  lb := 0
                else if inxtype^.form = subrange then
                  lb := inxtype^.min.ival;
                bs := aeltype^.size
              end
              else
                error(116);
          if sy = comma then
            insymbol
          else
            error(20);
          expression(fsys + [comma, rparent], False);
          load;
          if gattr.typtr <> nil then
            if gattr.typtr^.form <> scalar then
              error(116)
            else if not comptypes(lsp, gattr.typtr) then
              error(116);
          gen2(51 { ldc }, 1, lb);
          gen0(21 { sbi });
          gen2(51 { ldc }, 1, bs);
          gen0(15 { mpi });
          if sy = comma then
            insymbol
          else
            error(20);
          variable(fsys + [rparent], False);
          loadaddress;
          if gattr.typtr <> nil then
            with gattr.typtr^ do
              if form = arrays then
              begin
                if not comptypes(aeltype, lsp1) then
                  error(116)
              end
              else
                error(116);
          if (gattr.typtr <> nil) and (lattr.typtr <> nil) then
            gen2(62 { pck }, gattr.typtr^.size, lattr.typtr^.size)
        end { packprocedure };

        procedure unpackprocedure;
        var
          lsp, lsp1: stp;
          lattr, lattr1: attr;
          lb, bs: Integer;
        begin
          variable(fsys + [comma, rparent], False);
          loadaddress;
          lattr := gattr;
          lsp := nil;
          lsp1 := nil;
          lb := 1;
          bs := 1;
          if gattr.typtr <> nil then
            with gattr.typtr^ do
              if form = arrays then
                lsp1 := aeltype
              else
                error(116);
          if sy = comma then
            insymbol
          else
            error(20);
          variable(fsys + [comma, rparent], False);
          loadaddress;
          lattr1 := gattr;
          if gattr.typtr <> nil then
            with gattr.typtr^ do
              if form = arrays then
              begin
                if not comptypes(aeltype, lsp1) then
                  error(116);
                if (inxtype = charptr) or (inxtype = boolptr) then
                  lb := 0
                else if inxtype^.form = subrange then
                  lb := inxtype^.min.ival;
                bs := aeltype^.size;
                lsp := inxtype;
              end
              else
                error(116);
          if sy = comma then
            insymbol
          else
            error(20);
          expression(fsys + [rparent], False);
          load;
          if gattr.typtr <> nil then
            if gattr.typtr^.form <> scalar then
              error(116)
            else if not comptypes(lsp, gattr.typtr) then
              error(116);
          gen2(51 { ldc }, 1, lb);
          gen0(21 { sbi });
          gen2(51 { ldc }, 1, bs);
          gen0(15 { mpi });
          if (lattr.typtr <> nil) and (lattr1.typtr <> nil) then
            gen2(63 { upk }, lattr.typtr^.size, lattr1.typtr^.size)
        end { unpackprocedure };

        procedure newdisposeprocedure(disp: Boolean);
        label
          1;
        var
          lsp, lsp1, lsp2: stp;
          lsize: addrrange;
          lval: valu;
          tagc: Integer;
          tagrec: Boolean;
        begin
          if disp then
          begin
            expression(fsys + [comma, rparent], False);
            load
          end
          else
          begin
            variable(fsys + [comma, rparent], False);
            loadaddress
          end;
          lsp := nil;
          lsize := 0;
          tagc := 0;
          if gattr.typtr <> nil then
            with gattr.typtr^ do
              if form = pointer then
              begin
                if eltype <> nil then
                begin
                  lsize := eltype^.size;
                  if eltype^.form = records then
                    lsp := eltype^.recvar
                end
              end
              else
                error(116);
          tagrec := taggedrec(lsp);
          while sy = comma do
          begin
            insymbol;
            constant(fsys + [comma, rparent], lsp1, lval);
            lsp2 := lsp1;
            { check to insert here: is constant in tagfieldtype range }
            if lsp = nil then
              error(158)
            else if lsp^.form <> tagfld then
              error(162)
            else if lsp^.tagfieldp <> nil then
              if _string(lsp1) or (lsp1 = realptr) then
                error(159)
              else if comptypes(lsp^.tagfieldp^.idtype, lsp1) then
              begin
                lsp1 := lsp^.fstvar;
                while lsp1 <> nil do
                  with lsp1^ do
                    if varval.ival = lval.ival then
                    begin
                      lsize := size;
                      lsp := subvar;
                      if debug then
                      begin
                        if lsp2 = charptr then
                          gen2(51 { ldc }, 6, varval.ival)
                        else
                          gen2(51 { ldc }, 1, varval.ival)
                      end;
                      tagc := tagc + 1;
                      goto 1
                    end
                    else
                      lsp1 := nxtvar;
                lsize := lsp^.size;
                lsp := nil;
              end
              else
                error(116);
            1:
          end;
          if debug and tagrec then
            gen2(51 { ldc }, 1, tagc);
          gen2(51 { ldc }, 1, lsize);
          if debug and tagrec then
          begin
            if lkey = 9 then
              gen1(30 { csp }, 42 { nwl })
            else
              gen1(30 { csp }, 43 { dsl });
            mesl(tagc * intsize)
          end
          else
          begin
            if lkey = 9 then
              gen1(30 { csp }, 12 { New })
            else
              gen1(30 { csp }, 29 { dsp })
          end;
        end { newdisposeprocedure };

        procedure absfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr = intptr then
              gen0(0 { abi })
            else if gattr.typtr = realptr then
              gen0(1 { abr })
            else
            begin
              error(125);
              gattr.typtr := intptr
            end
        end { absfunction };

        procedure sqrfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr = intptr then
              gen0(24 { sqi })
            else if gattr.typtr = realptr then
              gen0(25 { sqr })
            else
            begin
              error(125);
              gattr.typtr := intptr
            end
        end { sqrfunction };

        procedure truncfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr <> realptr then
              error(125);
          gen0(27 { trc });
          gattr.typtr := intptr
        end { truncfunction };

        procedure roundfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr <> realptr then
              error(125);
          gen0(61 { rnd });
          gattr.typtr := intptr
        end { roundfunction };

        procedure oddfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr <> intptr then
              error(125);
          gen0(20 { odd });
          gattr.typtr := boolptr
        end { oddfunction };

        procedure ordfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr^.form >= power then
              error(125);
          gen0t(58 { Ord }, gattr.typtr);
          gattr.typtr := intptr
        end { ordfunction };

        procedure chrfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr <> intptr then
              error(125);
          gen0(59 { chr });
          gattr.typtr := charptr
        end { chrfunction };

        procedure predsuccfunction;
        begin
          if gattr.typtr <> nil then
            if gattr.typtr^.form <> scalar then
              error(125);
          if lkey = 7 then
            gen1t(31 { dec }, 1, gattr.typtr)
          else
            gen1t(34 { inc }, 1, gattr.typtr)
        end { predsuccfunction };

        procedure eofeolnfunction;
        begin
          if sy = lparent then
          begin
            insymbol;
            variable(fsys + [rparent], False);
            if sy = rparent then
              insymbol
            else
              error(4);
            loadaddress
          end
          else
          begin
            if not inputhdf then
              error(175);
            gen1(37 { lao }, inputptr^.vaddr);
            gattr.typtr := textptr
          end;
          if gattr.typtr <> nil then
            if gattr.typtr^.form <> files then
              error(125)
            else if (lkey = 10) and (gattr.typtr <> textptr) then
              error(116);
          if lkey = 9 then
          begin
            if gattr.typtr = textptr then
              gen1(30 { csp }, 44 { Eof })
            else
              gen1(30 { csp }, 45 { efb })
          end
          else
            gen1(30 { csp }, 14 { eln });
          gattr.typtr := boolptr
        end { eofeolnfunction };

        procedure callnonstandard(fcp: ctp);
        var
          nxt, lcp: ctp;
          lsp: stp;
          lkind: idkind;
          lb: Boolean;
          locpar, llc: addrrange;
          varp: Boolean;
          lsize: addrrange;

          procedure compparam(pla, plb: ctp);
          begin
            while (pla <> nil) and (plb <> nil) do
            begin
              if not comptypes(pla^.idtype, plb^.idtype) then
                error(189);
              pla := pla^.next;
              plb := plb^.next
            end;
            if (pla <> nil) or (plb <> nil) then
              error(189)
          end { compparam };

        begin
          locpar := 0;
          with fcp^ do
          begin
            nxt := pflist;
            lkind := pfkind;
            if pfkind = actual then
            begin { it's a system call }
              if not externl then
                gen1(41 { mst }, level - pflev)
            end
            else
              gen1(41 { mst }, level - pflev) { its an indirect }
          end;
          if sy = lparent then
          begin
            llc := lc;
            repeat
              lb := False; { decide whether proc/func must be passed }
              if nxt = nil then
                error(126)
              else
                lb := nxt^.klass in [proc, func];
              insymbol;
              if lb then { pass function or procedure }
              begin
                if sy <> ident then
                begin
                  error(2);
                  skip(fsys + [comma, rparent])
                end
                else if nxt <> nil then
                begin
                  if nxt^.klass = proc then
                    searchid([proc], lcp)
                  else
                  begin
                    searchid([func], lcp);
                    { compare result types }
                    if not comptypes(lcp^.idtype, nxt^.idtype) then
                      error(128)
                  end;
                  { compare parameter lists }
                  if (nxt^.klass in [proc, func]) and
                    (lcp^.klass in [proc, func]) then
                    compparam(nxt^.pflist, lcp^.pflist);
                  if lcp^.pfkind = actual then
                    genlpa(lcp^.pfname, level - lcp^.pflev)
                  else
                    gen2(74 { lip }, level - lcp^.pflev, lcp^.pfaddr);
                  locpar := locpar + ptrsize * 2;
                  insymbol;
                  if not (sy in fsys + [comma, rparent]) then
                  begin
                    error(6);
                    skip(fsys + [comma, rparent])
                  end
                end
              end
              else
              begin
                varp := False;
                if nxt <> nil then
                  varp := nxt^.vkind = formal;
                if varp then
                  variable(fsys + [comma, rparent], varp)
                else
                  expression(fsys + [comma, rparent], varp);
                if gattr.typtr <> nil then
                begin
                  if nxt <> nil then
                  begin
                    lsp := nxt^.idtype;
                    if lsp <> nil then
                    begin
                      if (nxt^.vkind = actual) then
                      begin
                        if lsp^.form <= power then
                        begin
                          load;
                          if debug then
                            checkbnds(lsp);
                          if comptypes(realptr, lsp)
                            and (gattr.typtr = intptr) then
                          begin
                            gen0(10 { flt });
                            gattr.typtr := realptr
                          end;
                          locpar := locpar + lsp^.size;
                          alignu(parmptr, locpar);
                        end
                        else
                        begin
                          loadaddress;
                          locpar := locpar + ptrsize;
                          alignu(parmptr, locpar)
                        end;
                        if not comptypes(lsp, gattr.typtr) then
                          error(142)
                      end
                      else
                      begin
                        if gattr.kind = varbl then
                        begin
                          if gattr.packcom then
                            error(197);
                          if gattr.tagfield then
                            error(198);
                          loadaddress;
                          locpar := locpar + ptrsize;
                          alignu(parmptr, locpar);
                        end
                        else
                          error(154);
                        if lsp <> gattr.typtr then
                          error(199)
                      end

                    end
                  end
                end
              end;
              if nxt <> nil then
                nxt := nxt^.next
            until sy <> comma;
            lc := llc;
            if sy = rparent then
              insymbol
            else
              error(4)
          end { if lparent };
          if lkind = actual then
          begin
            if nxt <> nil then
              error(126);
            with fcp^ do
            begin
              if externl then
                gen1(30 { csp }, pfname)
              else
              begin
                gencupent(46 { cup }, locpar, pfname);
                if fcp^.klass = func then
                begin
                  { add size of function result back to stack }
                  lsize := fcp^.idtype^.size;
                  alignu(parmptr, lsize);
                  mesl(-lsize)
                end
              end
            end
          end
          else
          begin { call procedure or function parameter }
            gen2(50 { lda }, level - fcp^.pflev, fcp^.pfaddr);
            gen1(67 { cip }, locpar);
            mesl(locpar); { remove stack parameters }
            if fcp^.klass = func then
            begin
              { add size of function result back to stack }
              lsize := fcp^.idtype^.size;
              alignu(parmptr, lsize);
              mesl(-lsize)
            end
          end;
          gattr.typtr := fcp^.idtype
        end { callnonstandard };

      begin
        if fcp^.pfdeckind = standard then
        begin
          lkey := fcp^.key;
          if fcp^.klass = proc then
          begin
            if not (lkey in [5, 6, 11, 12, 17]) then
              if sy = lparent then
                insymbol
              else
                error(9);
            case lkey of
               1,
               2,
               3,
               4:
                getputresetrewriteprocedure;
              17:
                pageprocedure;
               5,
              11:
                readprocedure;
               6,
              12:
                writeprocedure;
               7:
                packprocedure;
               8:
                unpackprocedure;
               9,
              18:
                newdisposeprocedure(lkey = 18);
              10,
              13:
                error(399)
            end;
            if not (lkey in [5, 6, 11, 12, 17]) then
              if sy = rparent then
                insymbol
              else
                error(4)
          end
          else
          begin
            if (lkey <= 8) or (lkey = 16) then
            begin
              if sy = lparent then
                insymbol
              else
                error(9);
              expression(fsys + [rparent], False);
              load
            end;
            case lkey of
               1:
                 absfunction;
               2:
                 sqrfunction;
               3:
                 truncfunction;
              16:
                roundfunction;
               4:
                 oddfunction;
               5:
                 ordfunction;
               6:
                 chrfunction;
               7,
               8:
                 predsuccfunction;
               9,
              10:
                eofeolnfunction
            end;
            if (lkey <= 8) or (lkey = 16) then
              if sy = rparent then
                insymbol
              else
                error(4)
          end;
        end { standard procedures and functions }
        else
          callnonstandard(fcp)
      end { call };

      procedure expression;
      var
        lattr: attr;
        lop: operator;
        typind: Char;
        lsize: addrrange;

        procedure simpleexpression(fsys: setofsys; threaten: Boolean);
        var
          lattr: attr;
          lop: operator;
          signed: Boolean;

          procedure term(fsys: setofsys; threaten: Boolean);
          var
            lattr: attr;
            lop: operator;

            procedure factor(fsys: setofsys; threaten: Boolean);
            var
              lcp: ctp;
              lvp: csp;
              varpart: Boolean;
              cstpart: setty;
              lsp: stp;
              tattr, rattr: attr;
              test: Boolean;
            begin
              if not (sy in facbegsys) then
              begin
                error(58);
                skip(fsys + facbegsys);
                gattr.typtr := nil
              end;
              while sy in facbegsys do
              begin
                case sy of
                  { id }ident:
                    begin
                      searchid([konst, vars, field, func], lcp);
                      insymbol;
                      if lcp^.klass = func then
                      begin
                        call(fsys, lcp);
                        with gattr do
                        begin
                          kind := expr;
                          if typtr <> nil then
                            if typtr^.form = subrange then
                              typtr := typtr^.rangetype
                        end
                      end
                      else if lcp^.klass = konst then
                        with gattr, lcp^ do
                        begin
                          typtr := idtype;
                          kind := cst;
                          cval := values
                        end
                      else
                      begin
                        selector(fsys, lcp);
                        if threaten and (lcp^.klass = vars) then
                          with lcp^ do
                          begin
                            if vlev < level then
                              threat := True;
                            if forcnt > 0 then
                              error(195);
                          end;
                        if gattr.typtr <> nil then { elim.subr.types to }
                          with gattr, typtr^ do { simplify later tests }
                      end
                    end;
                  { cst }intconst:
                    begin
                      with gattr do
                      begin
                        typtr := intptr;
                        kind := cst;
                        cval := val
                      end;
                      insymbol
                    end;
                  realconst:
                    begin
                      with gattr do
                      begin
                        typtr := realptr;
                        kind := cst;
                        cval := val
                      end;
                      insymbol
                    end;
                  stringconst:
                    begin
                      with gattr do
                      begin
                        if lgth = 1 then
                          typtr := charptr
                        else
                        begin
                          New(lsp);
                          pshstc(lsp);
                          with lsp^ do
                          begin
                            aeltype := charptr;
                            form := arrays;
                            packing := True;
                            inxtype := nil;
                            size := lgth * charsize
                          end;
                          typtr := lsp
                        end;
                        kind := cst;
                        cval := val
                      end;
                      insymbol
                    end;
                  {  (  }lparent:
                    begin
                      insymbol;
                      expression(fsys + [rparent], False);
                      if sy = rparent then
                        insymbol
                      else
                        error(4)
                    end;
                  { not }notsy:
                    begin
                      insymbol;
                      factor(fsys, False);
                      load;
                      gen0(19 { not });
                      if gattr.typtr <> nil then
                        if gattr.typtr <> boolptr then
                        begin
                          error(135);
                          gattr.typtr := nil
                        end;
                    end;
                  { [ }lbrack:
                    begin
                      insymbol;
                      cstpart := [];
                      varpart := False;
                      New(lsp);
                      pshstc(lsp);
                      with lsp^ do
                      begin
                        elset := nil;
                        size := setsize;
                        form := power;
                        packing := False;
                        matchpack := False
                      end;
                      if sy = rbrack then
                      begin
                        with gattr do
                        begin
                          typtr := lsp;
                          kind := cst
                        end;
                        insymbol
                      end
                      else
                      begin
                        repeat
                          expression(fsys + [comma, range, rbrack], False);
                          rattr.typtr := nil;
                          if sy = range then
                          begin
                            insymbol;
                            { if the left side is not constant, load it
                              and coerce it to Integer now }
                            if gattr.kind <> cst then
                            begin
                              load;
                              if not comptypes(gattr.typtr, intptr) then
                                gen0t(58 { Ord }, gattr.typtr);
                            end;
                            tattr := gattr;
                            expression(fsys + [comma, rbrack], False);
                            rattr := gattr;
                            gattr := tattr;
                          end;
                          if gattr.typtr <> nil then
                            if (gattr.typtr^.form <> scalar) and
                              (gattr.typtr^.form <> subrange) then
                            begin
                              error(136);
                              gattr.typtr := nil
                            end
                            else if comptypes(gattr.typtr, realptr) then
                            begin
                              error(109);
                              gattr.typtr := nil
                            end
                            else if comptypes(lsp^.elset, gattr.typtr) then
                            begin
                              if rattr.typtr <> nil then
                              begin { x..y form }
                                if (rattr.typtr^.form <> scalar) and
                                  (rattr.typtr^.form <> subrange) then
                                begin
                                  error(136);
                                  rattr.typtr := nil
                                end
                                else if comptypes(rattr.typtr, realptr) then
                                begin
                                  error(109);
                                  rattr.typtr := nil
                                end
                                else if comptypes(lsp^.elset, rattr.typtr) then
                                begin
                                  if (gattr.kind = cst) and
                                    (rattr.kind = cst) then
                                    if (rattr.cval.ival < setlow) or
                                      (rattr.cval.ival > sethigh) or
                                      (gattr.cval.ival < setlow) or
                                      (gattr.cval.ival > sethigh) then
                                      error(304)
                                    else
                                      cstpart := cstpart +
                                        [gattr.cval.ival..rattr.cval.ival]
                                  else
                                  begin
                                    if gattr.kind = cst then
                                    begin
                                      load;
                                      if not comptypes(gattr.typtr, intptr) then
                                        gen0t(58 { Ord }, gattr.typtr)
                                    end;
                                    tattr := gattr;
                                    gattr := rattr;
                                    load;
                                    gattr := tattr;
                                    if not comptypes(rattr.typtr, intptr) then
                                      gen0t(58 { Ord }, rattr.typtr);
                                    gen0(64 { rgs });
                                    if varpart then
                                      gen0(28 { uni })
                                    else
                                      varpart := True
                                  end
                                end
                                else
                                  error(137)
                              end
                              else
                              begin
                                if gattr.kind = cst then
                                  if (gattr.cval.ival < setlow) or
                                    (gattr.cval.ival > sethigh) then
                                    error(304)
                                  else
                                    cstpart := cstpart + [gattr.cval.ival]
                                else
                                begin
                                  load;
                                  if not comptypes(gattr.typtr, intptr) then
                                    gen0t(58 { Ord }, gattr.typtr);
                                  gen0(23 { sgs });
                                  if varpart then
                                    gen0(28 { uni })
                                  else
                                    varpart := True
                                end
                              end;
                              lsp^.elset := gattr.typtr;
                              gattr.typtr := lsp
                            end
                            else
                              error(137);
                          test := sy <> comma;
                          if not test then
                            insymbol
                        until test;
                        if sy = rbrack then
                          insymbol
                        else
                          error(12)
                      end;
                      if varpart then
                      begin
                        if cstpart <> [] then
                        begin
                          New(lvp);
                          pshcst(lvp);
                          lvp^.pval := cstpart;
                          lvp^.cclass := pset;
                          if cstptrix = cstoccmax then
                            error(254)
                          else
                          begin
                            cstptrix := cstptrix + 1;
                            cstptr[cstptrix] := lvp;
                            gen2(51 { ldc }, 5, cstptrix);
                            gen0(28 { uni });
                            gattr.kind := expr
                          end
                        end
                      end
                      else
                      begin
                        New(lvp);
                        pshcst(lvp);
                        lvp^.cclass := pset;
                        lvp^.pval := cstpart;
                        gattr.cval.valp := lvp
                      end
                    end;
                  { nil }nilsy: with gattr do
                    begin
                      typtr := nilptr;
                      kind := cst;
                      cval.ival := nilval;
                      insymbol
                    end
                end;
                if not (sy in fsys) then
                begin
                  error(6);
                  skip(fsys + facbegsys)
                end
              end
            end { factor };

          begin
            factor(fsys + [mulop], threaten);
            while sy = mulop do
            begin
              load;
              lattr := gattr;
              lop := op;
              insymbol;
              factor(fsys + [mulop], threaten);
              load;
              if (lattr.typtr <> nil) and (gattr.typtr <> nil) then
                case lop of
                  { * }mul: if (lattr.typtr = intptr) and (gattr.typtr = intptr)
                    then
                      gen0(15 { mpi })
                    else
                    begin
                      if lattr.typtr = intptr then
                      begin
                        gen0(9 { flo });
                        lattr.typtr := realptr
                      end
                      else if gattr.typtr = intptr then
                      begin
                        gen0(10 { flt });
                        gattr.typtr := realptr
                      end;
                      if (lattr.typtr = realptr)
                        and (gattr.typtr = realptr) then
                        gen0(16 { mpr })
                      else if (lattr.typtr^.form = power)
                        and comptypes(lattr.typtr, gattr.typtr) then
                        gen0(12 { int })
                      else
                      begin
                        error(134);
                        gattr.typtr := nil
                      end
                    end;
                  {  /  }rdiv:
                    begin
                      if gattr.typtr = intptr then
                      begin
                        gen0(10 { flt });
                        gattr.typtr := realptr
                      end;
                      if lattr.typtr = intptr then
                      begin
                        gen0(9 { flo });
                        lattr.typtr := realptr
                      end;
                      if (lattr.typtr = realptr)
                        and (gattr.typtr = realptr) then
                        gen0(7 { dvr })
                      else
                      begin
                        error(134);
                        gattr.typtr := nil
                      end
                    end;
                  { div }idiv: if (lattr.typtr = intptr)
                    and (gattr.typtr = intptr) then
                      gen0(6 { dvi })
                    else
                    begin
                      error(134);
                      gattr.typtr := nil
                    end;
                  { mod }imod: if (lattr.typtr = intptr)
                    and (gattr.typtr = intptr) then
                      gen0(14 { mod })
                    else
                    begin
                      error(134);
                      gattr.typtr := nil
                    end;
                  { and }andop: if (lattr.typtr = boolptr)
                    and (gattr.typtr = boolptr) then
                      gen0(4 { and })
                    else
                    begin
                      error(134);
                      gattr.typtr := nil
                    end
                end
              else
                gattr.typtr := nil
            end
          end { term };

        begin { simpleexpression }
          signed := False;
          if (sy = addop) and (op in [plus, minus]) then
          begin
            signed := op = minus;
            insymbol
          end;
          term(fsys + [addop], threaten);
          if signed then
          begin
            load;
            if gattr.typtr = intptr then
              gen0(17 { ngi })
            else if gattr.typtr = realptr then
              gen0(18 { ngr })
            else
            begin
              error(134);
              gattr.typtr := nil
            end
          end;
          while sy = addop do
          begin
            load;
            lattr := gattr;
            lop := op;
            insymbol;
            term(fsys + [addop], threaten);
            load;
            if (lattr.typtr <> nil) and (gattr.typtr <> nil) then
              case lop of
                { + }plus:
                  if (lattr.typtr = intptr) and (gattr.typtr = intptr) then
                    gen0(2 { adi })
                  else
                  begin
                    if lattr.typtr = intptr then
                    begin
                      gen0(9 { flo });
                      lattr.typtr := realptr
                    end
                    else if gattr.typtr = intptr then
                    begin
                      gen0(10 { flt });
                      gattr.typtr := realptr
                    end;
                    if (lattr.typtr = realptr) and (gattr.typtr = realptr) then
                      gen0(3 { adr })
                    else if (lattr.typtr^.form = power)
                      and comptypes(lattr.typtr, gattr.typtr) then
                      gen0(28 { uni })
                    else
                    begin
                      error(134);
                      gattr.typtr := nil
                    end
                  end;
                { - }minus:
                  if (lattr.typtr = intptr) and (gattr.typtr = intptr) then
                    gen0(21 { sbi })
                  else
                  begin
                    if lattr.typtr = intptr then
                    begin
                      gen0(9 { flo });
                      lattr.typtr := realptr
                    end
                    else if gattr.typtr = intptr then
                    begin
                      gen0(10 { flt });
                      gattr.typtr := realptr
                    end;
                    if (lattr.typtr = realptr) and (gattr.typtr = realptr) then
                      gen0(22 { sbr })
                    else if (lattr.typtr^.form = power)
                      and comptypes(lattr.typtr, gattr.typtr) then
                      gen0(5 { dif })
                    else
                    begin
                      error(134);
                      gattr.typtr := nil
                    end
                  end;
                { or }orop:
                  if (lattr.typtr = boolptr) and (gattr.typtr = boolptr) then
                    gen0(13 { ior })
                  else
                  begin
                    error(134);
                    gattr.typtr := nil
                  end
              end
            else
              gattr.typtr := nil
          end
        end { simpleexpression };

      begin
        typind := ' ';
        simpleexpression(fsys + [relop], threaten);
        if sy = relop then
        begin
          if gattr.typtr <> nil then
            if gattr.typtr^.form <= power then
              load
            else
              loadaddress;
          lattr := gattr;
          lop := op;
          if lop = inop then
            if not comptypes(gattr.typtr, intptr) then
              gen0t(58 { Ord }, gattr.typtr);
          insymbol;
          simpleexpression(fsys, threaten);
          if gattr.typtr <> nil then
            if gattr.typtr^.form <= power then
              load
            else
              loadaddress;
          if (lattr.typtr <> nil) and (gattr.typtr <> nil) then
            if lop = inop then
              if gattr.typtr^.form = power then
                if comptypes(lattr.typtr, gattr.typtr^.elset) then
                  gen0(11 { inn })
                else
                begin
                  error(129);
                  gattr.typtr := nil
                end
              else
              begin
                error(130);
                gattr.typtr := nil
              end
            else
            begin
              if lattr.typtr <> gattr.typtr then
                if lattr.typtr = intptr then
                begin
                  gen0(9 { flo });
                  lattr.typtr := realptr
                end
                else if gattr.typtr = intptr then
                begin
                  gen0(10 { flt });
                  gattr.typtr := realptr
                end;
              if comptypes(lattr.typtr, gattr.typtr) then
              begin
                lsize := lattr.typtr^.size;
                case lattr.typtr^.form of
                  scalar:
                    if lattr.typtr = realptr then
                      typind := 'r'
                    else if lattr.typtr = boolptr then
                      typind := 'b'
                    else if lattr.typtr = charptr then
                      typind := 'c'
                    else
                      typind := 'i';
                  pointer:
                    begin
                      if lop in [ltop, leop, gtop, geop] then
                        error(131);
                      typind := 'a'
                    end;
                  power:
                    begin
                      if lop in [ltop, gtop] then
                        error(132);
                      typind := 's'
                    end;
                  arrays:
                    begin
                      if not _string(lattr.typtr) then
                        error(134);
                      typind := 'm'
                    end;
                  records:
                    begin
                      error(134);
                      typind := 'm'
                    end;
                  files:
                    begin
                      error(133);
                      typind := 'f'
                    end
                end;
                case lop of
                  ltop:
                    gen2(53 { les }, Ord(typind), lsize);
                  leop:
                    gen2(52 { leq }, Ord(typind), lsize);
                  gtop:
                    gen2(49 { grt }, Ord(typind), lsize);
                  geop:
                    gen2(48 { geq }, Ord(typind), lsize);
                  neop:
                    gen2(55 { neq }, Ord(typind), lsize);
                  eqop:
                    gen2(47 { equ }, Ord(typind), lsize)
                end
              end
              else
                error(129)
            end;
          gattr.typtr := boolptr;
          gattr.kind := expr
        end { sy = relop }
      end { expression };

      procedure assignment(fcp: ctp);
      var
        lattr, lattr2: attr;
        tagasc: Boolean;
      begin
        tagasc := False;
        selector(fsys + [becomes], fcp);
        if sy = becomes then
        begin
          { if function result, set assigned }
          if fcp^.klass = func then
            fcp^.asgn := True
          else if fcp^.klass = vars then
            with fcp^ do
            begin
              if vlev < level then
                threat := True;
              if forcnt > 0 then
                error(195)
            end;
          if gattr.kind = varbl then
            tagasc := gattr.tagfield and debug;
          lattr2 := gattr; { save access before load }
          if gattr.typtr <> nil then
            if (gattr.access <> drct) or (gattr.typtr^.form > power) or
              tagasc then { if tag checking, force address load }
              loadaddress;
          lattr := gattr;
          insymbol;
          expression(fsys, False);
          if gattr.typtr <> nil then
            if gattr.typtr^.form <= power then
              load
            else
              loadaddress;
          if (lattr.typtr <> nil) and (gattr.typtr <> nil) then
          begin
            if comptypes(realptr, lattr.typtr) and (gattr.typtr = intptr) then
            begin
              gen0(10 { flt });
              gattr.typtr := realptr
            end;
            if comptypes(lattr.typtr, gattr.typtr) then
            begin
              if filecomponent(gattr.typtr) then
                error(191);
              with lattr2 do
                if kind = varbl then
                begin
                  if access = indrct then
                    if debug and tagfield and ptrref then
                      { check tag assignment to pointer record }
                      gen2(81 { cta }, idplmt, taglvl);
                  if debug and tagfield then
                    gen2(82 { ivt }, vartagoff, varssize)
                end;
              { if tag checking, bypass normal store }
              if tagasc then
                gen0t(26 { sto }, lattr.typtr)
              else
                case lattr.typtr^.form of
                  scalar,
                  subrange,
                  power:
                    begin
                      if debug then
                        checkbnds(lattr.typtr);
                      store(lattr)
                    end;
                  pointer:
                    begin
                      if debug then
                      begin
                        if taggedrec(lattr.typtr^.eltype) then
                          gen2t(80 { ckl }, 0, maxaddr, nilptr)
                        else
                          gen2t(45 { chk }, 0, maxaddr, nilptr);
                      end;
                      store(lattr)
                    end;
                  arrays,
                    records: gen1(40 { mov }, lattr.typtr^.size);
                  files: error(146)
                end;
            end
            else
              error(129)
          end
        end { sy = becomes }
        else
          error(51)
      end { assignment };

      procedure gotostatement;
      var
        llp: lbp;
        ttop, ttop1: disprange;

      begin
        if sy = intconst then
        begin
          ttop := top;
          while display[ttop].occur <> blck do
            ttop := ttop - 1;
          ttop1 := ttop;
          repeat
            searchlabel(llp, ttop); { find label }
            if llp <> nil then
              with llp^ do
              begin
                refer := True;
                if defined then
                  if slevel > stalvl then { defining point level greater than
                                            present statement level }
                    error(185) { goto references deeper nested statement }
                  else if (slevel > 1) and not bact then
                    error(187); { Goto references label in different nested
                                  statement }
                { establish the minimum statement level a goto appeared at }
                if minlvl > stalvl then
                  minlvl := stalvl;
                if ttop = ttop1 then
                  genujpxjp(57 { ujp }, labname)
                else
                begin { interprocedural goto }
                  genipj(66 { ipj }, level - vlevel, labname);
                  ipcref := True
                end
              end;
            ttop := ttop - 1
          until (llp <> nil) or (ttop = 0);
          if llp = nil then
          begin
            error(167); { undeclared label }
            newlabel(llp); { create dummy label in current context }
            llp^.refer := True
          end;
          insymbol
        end
        else
          error(15)
      end { gotostatement };

      procedure compoundstatement;
      var
        test: Boolean;
      begin
        addlvl;
        repeat
          repeat
            statement(fsys + [semicolon, endsy])
          until not (sy in statbegsys);
          test := sy <> semicolon;
          if not test then
            insymbol
        until test;
        if sy = endsy then
          insymbol
        else
          error(13);
        sublvl
      end { compoundstatemenet };

      procedure ifstatement;
      var
        lcix1, lcix2: Integer;
      begin
        expression(fsys + [thensy], False);
        genlabel(lcix1);
        genfjp(lcix1);
        if sy = thensy then
          insymbol
        else
          error(52);
        addlvl;
        statement(fsys + [elsesy]);
        sublvl;
        if sy = elsesy then
        begin
          genlabel(lcix2);
          genujpxjp(57 { ujp }, lcix2);
          putlabel(lcix1);
          insymbol;
          addlvl;
          statement(fsys);
          sublvl;
          putlabel(lcix2)
        end
        else
          putlabel(lcix1)
      end { ifstatement };

      procedure casestatement;
      label
        1;
      var
        lsp, lsp1: stp;
        fstptr, lpt1, lpt2, lpt3: cip;
        lval: valu;
        laddr, lcix, lcix1, lmin, lmax: Integer;
        test: Boolean;
      begin
        expression(fsys + [ofsy, comma, colon], False);
        load;
        genlabel(lcix);
        lsp := gattr.typtr;
        if lsp <> nil then
          if (lsp^.form <> scalar) or (lsp = realptr) then
          begin
            error(144);
            lsp := nil
          end
          else if not comptypes(lsp, intptr) then
            gen0t(58 { Ord }, lsp);
        genujpxjp(57 { ujp }, lcix);
        mesl(-intsize); { remove selector from stack }
        if sy = ofsy then
          insymbol
        else
          error(8);
        fstptr := nil;
        genlabel(laddr);
        repeat
          lpt3 := nil;
          genlabel(lcix1);
          if not (sy in [semicolon, endsy]) then
          begin
            repeat
              constant(fsys + [comma, colon], lsp1, lval);
              if lsp <> nil then
                if comptypes(lsp, lsp1) then
                begin
                  lpt1 := fstptr;
                  lpt2 := nil;
                  while lpt1 <> nil do
                    with lpt1^ do
                    begin
                      if cslab <= lval.ival then
                      begin
                        if cslab = lval.ival then
                          error(156);
                        goto 1
                      end;
                      lpt2 := lpt1;
                      lpt1 := next
                    end;
                  1: getcas(lpt3);
                  with lpt3^ do
                  begin
                    next := lpt1;
                    cslab := lval.ival;
                    csstart := lcix1
                  end;
                  if lpt2 = nil then
                    fstptr := lpt3
                  else
                    lpt2^.next := lpt3
                end
                else
                  error(147);
              test := sy <> comma;
              if not test then
                insymbol
            until test;
            if sy = colon then
              insymbol
            else
              error(5);
            putlabel(lcix1);
            repeat
              addlvl;
              statement(fsys + [semicolon]);
              sublvl
            until not (sy in statbegsys);
            if lpt3 <> nil then
              genujpxjp(57 { ujp }, laddr);
          end;
          test := sy <> semicolon;
          if not test then
            insymbol
        until test;
        putlabel(lcix);
        mesl(+intsize); { put selector back on stack }
        if fstptr <> nil then
        begin
          lmax := fstptr^.cslab;
          { reverse pointers }
          lpt1 := fstptr;
          fstptr := nil;
          repeat
            lpt2 := lpt1^.next;
            lpt1^.next := fstptr;
            fstptr := lpt1;
            lpt1 := lpt2
          until lpt1 = nil;
          lmin := fstptr^.cslab;
          if lmax - lmin < cixmax then
          begin
            gen2t(45 { chk }, lmin, lmax, intptr);
            gen2(51 { ldc }, 1, lmin);
            gen0(21 { sbi });
            genlabel(lcix);
            genujpxjp(44 { xjp }, lcix);
            putlabel(lcix);
            repeat
              with fstptr^ do
              begin
                while cslab > lmin do
                begin
                  gen0(60 { ujc error });
                  lmin := lmin + 1
                end;
                genujpxjp(57 { ujp }, csstart);
                lpt1 := fstptr;
                fstptr := next;
                lmin := lmin + 1;
                putcas(lpt1);
              end
            until fstptr = nil;
            putlabel(laddr)
          end
          else
          begin
            error(157);
            repeat
              with fstptr^ do
              begin
                lpt1 := fstptr;
                fstptr := next;
                putcas(lpt1);
              end
            until fstptr = nil
          end
        end;
        if sy = endsy then
          insymbol
        else
          error(13)
      end { casestatement };

      procedure repeatstatement;
      var
        laddr: Integer;
      begin
        genlabel(laddr);
        putlabel(laddr);
        addlvl;
        repeat
          statement(fsys + [semicolon, untilsy]);
          if sy in statbegsys then
            error(14)
        until not (sy in statbegsys);
        while sy = semicolon do
        begin
          insymbol;
          repeat
            statement(fsys + [semicolon, untilsy]);
            if sy in statbegsys then
              error(14);
          until not (sy in statbegsys);
        end;
        if sy = untilsy then
        begin
          insymbol;
          expression(fsys, False);
          genfjp(laddr)
        end
        else
          error(53);
        sublvl
      end { repeatstatement };

      procedure whilestatement;
      var
        laddr, lcix: Integer;
      begin
        genlabel(laddr);
        putlabel(laddr);
        expression(fsys + [dosy], False);
        genlabel(lcix);
        genfjp(lcix);
        if sy = dosy then
          insymbol
        else
          error(54);
        addlvl;
        statement(fsys);
        sublvl;
        genujpxjp(57 { ujp }, laddr);
        putlabel(lcix)
      end { whilestatement };

      procedure forstatement;
      var
        lattr: attr;
        lsy: symbol;
        lcix, laddr: Integer;
        llc, lcs: addrrange;
        typind: Char; {  added for typing [sam]  }
        typ: stp;
      begin
        lcp := nil;
        llc := lc;
        lsy := othersy;
        lcs := 0;
        with lattr do
        begin
          typtr := nil;
          kind := varbl;
          access := drct;
          vlevel := level;
          dplmt := 0;
          packing := False
        end;
        typind := 'i'; {  default to Integer [sam]  }
        if sy = ident then
        begin
          searchid([vars], lcp);
          with lcp^, lattr do
          begin
            typtr := idtype;
            kind := varbl;
            packing := False;
            if threat or (forcnt > 0) then
              error(195);
            forcnt := forcnt + 1;
            if vkind = actual then
            begin
              access := drct;
              vlevel := vlev;
              if vlev <> level then
                error(183);
              dplmt := vaddr
            end
            else
            begin
              error(155);
              typtr := nil
            end
          end;
          {  determine type of control variable [sam]  }
          if lattr.typtr = boolptr then
            typind := 'b'
          else if lattr.typtr = charptr then
            typind := 'c';
          if lattr.typtr <> nil then
            if (lattr.typtr^.form > subrange)
              or comptypes(realptr, lattr.typtr) then
            begin
              error(143);
              lattr.typtr := nil
            end;
          insymbol
        end
        else
        begin
          error(2);
          skip(fsys + [becomes, tosy, downtosy, dosy])
        end;
        if sy = becomes then
        begin
          insymbol;
          expression(fsys + [tosy, downtosy, dosy], False);
          typ := basetype(gattr.typtr); { get base type }
          if typ <> nil then
            if typ^.form <> scalar then
              error(144)
            else if comptypes(lattr.typtr, gattr.typtr) then
            begin
              load;
              alignd(intptr, lc);
              { store start to temp }
              gen2t(56 { str }, 0, lc - intsize, intptr);
            end
            else
              error(145)
        end
        else
        begin
          error(51);
          skip(fsys + [tosy, downtosy, dosy])
        end;
        if sy in [tosy, downtosy] then
        begin
          lsy := sy;
          insymbol;
          expression(fsys + [dosy], False);
          typ := basetype(gattr.typtr); { get base type }
          if typ <> nil then
            if typ^.form <> scalar then
              error(144)
            else if comptypes(lattr.typtr, gattr.typtr) then
            begin
              load;
              alignd(intptr, lc);
              if not comptypes(lattr.typtr, intptr) then
                gen0t(58 { Ord }, gattr.typtr);
              gen2t(56 { str }, 0, lc - intsize * 2, intptr);
              { set initial value of index }
              gen2t(54 { lod }, 0, lc - intsize, intptr);
              if debug and (lattr.typtr <> nil) then
                checkbnds(lattr.typtr);
              store(lattr);
              genlabel(laddr);
              putlabel(laddr);
              gattr := lattr;
              load;
              if not comptypes(gattr.typtr, intptr) then
                gen0t(58 { Ord }, gattr.typtr);
              gen2t(54 { lod }, 0, lc - intsize * 2, intptr);
              lcs := lc;
              lc := lc - intsize * 2;
              if lc < lcmin then
                lcmin := lc;
              if lsy = tosy then
                gen2(52 { leq }, Ord(typind), 1)
              else
                gen2(48 { geq }, Ord(typind), 1);
            end
            else
              error(145)
        end
        else
        begin
          error(55);
          skip(fsys + [dosy])
        end;
        genlabel(lcix);
        genujpxjp(33 { fjp }, lcix);
        if sy = dosy then
          insymbol
        else
          error(54);
        addlvl;
        statement(fsys);
        sublvl;
        gattr := lattr;
        load;
        if not comptypes(gattr.typtr, intptr) then
          gen0t(58 { Ord }, gattr.typtr);
        gen2t(54 { lod }, 0, lcs - intsize * 2, intptr);
        gen2(47 { equ }, Ord(typind), 1);
        genujpxjp(73 { tjp }, lcix);
        gattr := lattr;
        load;
        if lsy = tosy then
          gen1t(34 { inc }, 1, gattr.typtr)
        else
          gen1t(31 { dec }, 1, gattr.typtr);
        if debug and (lattr.typtr <> nil) then
          checkbnds(lattr.typtr);
        store(lattr);
        genujpxjp(57 { ujp }, laddr);
        putlabel(lcix);
        gattr := lattr;
        loadaddress;
        gen0(79 { inv });
        lc := llc;
        if lcp <> nil then
          lcp^.forcnt := lcp^.forcnt - 1
      end { forstatement };

      procedure withstatement;
      var
        lcp: ctp;
        lcnt1: disprange;
        llc: addrrange;
        test: Boolean;
      begin
        lcnt1 := 0;
        llc := lc;
        repeat
          if sy = ident then
          begin
            searchid([vars, field], lcp);
            insymbol
          end
          else
          begin
            error(2);
            lcp := uvarptr
          end;
          selector(fsys + [comma, dosy], lcp);
          if gattr.typtr <> nil then
            if gattr.typtr^.form = records then
              if top < displimit then
              begin
                top := top + 1;
                lcnt1 := lcnt1 + 1;
                with display[top] do
                begin
                  fname := gattr.typtr^.fstfld;
                  flabel := nil;
                  flabel := nil;
                  fconst := nil;
                  fstruct := nil;
                  packing := gattr.packing;
                  packcom := gattr.packcom;
                  ptrref := gattr.ptrref
                end;
                if gattr.access = drct then
                  with display[top] do
                  begin
                    occur := crec;
                    clev := gattr.vlevel;
                    cdspl := gattr.dplmt
                  end
                else
                begin
                  loadaddress;
                  alignd(nilptr, lc);
                  lc := lc - ptrsize;
                  gen2t(56 { str }, 0, lc, nilptr);
                  with display[top] do
                  begin
                    occur := vrec;
                    vdspl := lc
                  end;
                  if lc < lcmin then
                    lcmin := lc
                end
              end
              else
                error(250)
            else
              error(140);
          test := sy <> comma;
          if not test then
            insymbol
        until test;
        if sy = dosy then
          insymbol
        else
          error(54);
        addlvl;
        statement(fsys);
        sublvl;
        { purge display levels }
        while lcnt1 > 0 do
        begin
          { don't recycle the record context }
          display[top].fname := nil;
          putdsp(top); { purge }
          top := top - 1;
          lcnt1 := lcnt1 - 1; { count off }
        end;
        lc := llc;
      end { withstatement };

    begin { statement }
      if sy = intconst then { label }
      begin
        searchlabel(llp, level); { search label }
        if llp <> nil then
          with llp^ do
          begin { found }
            if defined then
              error(165); { multidefined label }
            bact := True; { set in active block now }
            slevel := stalvl; { establish statement level }
            defined := True; { set defined }
            if ipcref and (stalvl > 1) then
              error(184) { intraprocedure goto does not reference outter block }
            else if minlvl < stalvl then
              { Label referenced by goto at lesser statement level or
                differently nested statement }
              error(186);
            putlabel(labname); { Output label to intermediate }
          end
        else
        begin { not found }
          error(167); { undeclared label }
          newlabel(llp) { create a dummy level }
        end;
        insymbol;
        if sy = colon then
          insymbol
        else
          error(5)
      end;
      if not (sy in fsys + [ident]) then
      begin
        error(6);
        skip(fsys)
      end;
      if sy in statbegsys + [ident] then
      begin
        case sy of
          ident:
            begin
              searchid([vars, field, func, proc], lcp);
              insymbol;
              if lcp^.klass = proc then
                call(fsys, lcp)
              else
                assignment(lcp)
            end;
          beginsy:
            begin
              insymbol;
              compoundstatement
            end;
          gotosy:
            begin
              insymbol;
              gotostatement
            end;
          ifsy:
            begin
              insymbol;
              ifstatement
            end;
          casesy:
            begin
              insymbol;
              casestatement
            end;
          whilesy:
            begin
              insymbol;
              whilestatement
            end;
          repeatsy:
            begin
              insymbol;
              repeatstatement
            end;
          forsy:
            begin
              insymbol;
              forstatement
            end;
          withsy:
            begin
              insymbol;
              withstatement
            end
        end;
        if not (sy in [semicolon, endsy, elsesy, untilsy]) then
        begin
          error(6);
          skip(fsys)
        end
      end
    end { statement };

  begin { body }
    if fprocp <> nil then
      entname := fprocp^.pfname
    else
      genlabel(entname);
    cstptrix := 0;
    topnew := 0;
    topmin := 0;
    putlabel(entname);
    genlabel(segsize);
    genlabel(stackbot);
    genlabel(gblsize);
    gencupent(32 { ents }, 1, segsize);
    gencupent(32 { ente }, 2, stackbot);
    if fprocp <> nil then { copy multiple values into local cells }
    begin
      llc1 := lcaftermarkstack;
      lcp := fprocp^.pflist;
      while lcp <> nil do
        with lcp^ do
        begin
          if klass = vars then
            if idtype <> nil then
              if idtype^.form > power then
              begin
                llc1 := llc1 - ptrsize;
                alignd(parmptr, llc1);
                if vkind = actual then
                begin
                  gen2(50 { lda }, 0, vaddr);
                  gen2t(54 { lod }, 0, llc1, nilptr);
                  gen1(40 { mov }, idtype^.size);
                end
              end
              else
              begin
                llc1 := llc1 - idtype^.size;
                alignd(parmptr, llc1);
              end;
          lcp := lcp^.next;
        end;
    end;
    lcmin := lc;
    addlvl;
    repeat
      repeat
        statement(fsys + [semicolon, endsy])
      until not (sy in statbegsys);
      test := sy <> semicolon;
      if not test then
        insymbol
    until test;
    sublvl;
    if sy = endsy then
      insymbol
    else
      error(13);
    llp := display[top].flabel; { test for undefined and unreferenced labels }
    while llp <> nil do
      with llp^ do
      begin
        if not defined or not refer then
        begin
          if not defined then
            error(168);
          Writeln(Output);
          Write(Output, 'label ', labval: 11);
          if not refer then
            Write(' unreferenced');
          Writeln;
          Write(Output, ' ': chcnt + 16)
        end;
        llp := nextlab
      end;
    printed := False;
    chkrefs(display[top].fname, printed);
    if toterr = 0 then
      if topnew <> 0 then
        error(500); { stack should have wound to zero }
    if fprocp <> nil then
    begin
      if fprocp^.idtype = nil then
        gen1(42 { ret }, Ord('p'))
      else
        gen0t(42 { ret }, basetype(fprocp^.idtype));
      alignd(parmptr, lcmin);
      if prcode then
        begin
          Writeln(prr, 'l', segsize: 4, '=', lcmin: 1);
          Writeln(prr, 'l', stackbot: 4, '=', topmin: 1);
          Writeln(prr, 'g ', gc: 1)
        end;
    end
    else
    begin
      gen1(42 { ret }, Ord('p'));
      alignd(parmptr, lcmin);
      if prcode then
        begin
          Writeln(prr, 'l', segsize: 4, '=', lcmin: 1);
          Writeln(prr, 'l', stackbot: 4, '=', topmin: 1);
          Writeln(prr, 'g ', gc: 1);
          Writeln(prr, 'q');
        end;
      ic := 0;
      { generate call of main program; note that this call must be loaded
        at absolute address zero }
      gen1(41 { mst }, 0);
      gencupent(46 { cup }, 0, entname);
      gen0(29 { stp });
      if prcode then
        Writeln(prr, 'q');
      saveid := id;
      while fextfilep <> nil do
      begin
        with fextfilep^ do
          if not (strequri('input    ', filename) or
                  strequri('output   ', filename) or
                  strequri('prd      ', filename) or
                  strequri('prr      ', filename)) then
          begin
            id := filename;
            { hold the error in case not found, since this error
              occurs far from the original symbol }
            searchidne([vars], llcp);
            if llcp = nil then
            begin
              { a header file was never defined in a var statement }
              Writeln(Output);
              Writeln(Output, '**** Error: Undeclared external file ''',
                string(fextfilep^.filename): 8, '''');
              toterr := toterr + 1;
              llcp := uvarptr
            end;
            if llcp^.idtype <> nil then
              if llcp^.idtype^.form <> files then
              begin
                Writeln(Output);
                Writeln(Output, '**** Error: Undeclared external file ''',
                  string(fextfilep^.filename): 8, '''');
                toterr := toterr + 1
              end
          end;
        fp := fextfilep;
        fextfilep := fextfilep^.nextfile;
        putfil(fp);
      end;
      id := saveid;
      if prtables then
      begin
        Writeln(Output);
        printtables(True)
      end
    end;
  end { body };

begin { block }
  stalvl := 0; { clear statement nesting level }
  dp := True;
  repeat
    if sy = labelsy then
    begin
      insymbol;
      labeldeclaration
    end;
    if sy = constsy then
    begin
      insymbol;
      constdeclaration
    end;
    if sy = typesy then
    begin
      insymbol;
      typedeclaration
    end;
    if sy = varsy then
    begin
      insymbol;
      vardeclaration
    end;
    while sy in [procsy, funcsy] do
    begin
      lsy := sy;
      insymbol;
      procdeclaration(lsy)
    end;
    if sy <> beginsy then
    begin
      error(18);
      skip(fsys)
    end
  until (sy in statbegsys) or Eof(prd);
  dp := False;
  if sy = beginsy then
    insymbol
  else
    error(17);
  repeat
    body(fsys + [casesy]);
    if sy <> fsy then
    begin
      error(6);
      skip(fsys)
    end
  until ((sy = fsy) or (sy in blockbegsys)) or Eof(prd)
end { block };

procedure programme(fsys: setofsys);
var
  extfp: extfilep;
  extfn: Integer;
  extfilename: string;
begin
  extfn := 5;
  chkudtf := chkudtc; { finalize undefined tag checking flag }
  if sy = progsy then
  begin
    insymbol;
    if sy <> ident then
      error(2)
    else
      insymbol;
    if not (sy in [lparent, semicolon]) then
      error(14);
    if sy = lparent then
    begin
      repeat
        insymbol;
        if sy = ident then
        begin
          getfil(extfp);
          with extfp^ do
          begin
            filename := id;
            nextfile := fextfilep
          end;
          fextfilep := extfp;
          extfilename := Trim(id);
          { check 'input' or 'output' appears in header for defaults }
          if strequri('input    ', id) then
            inputhdf := True
          else if strequri('output   ', id) then
            outputhdf := True;
          insymbol;
          if not (sy in [comma, rparent, relop]) then
            error(20)
          else if sy = relop then
          begin
            insymbol;
            if sy <> stringconst then
              error(31)
            else
            begin
              extfilename := Trim(string(val.valp^.sval.str));
              insymbol
            end;
          end;
          if not (strequri('input    ', id) or
                  strequri('output   ', id) or
                  strequri('prd      ', id) or
                  strequri('prr      ', id)) then
          begin
            if prcode then
              Writeln(prr, 'x ', extfn: 1, ' ''', extfilename, '''');
            extfn := extfn + 1;
          end;
        end
        else
          error(2)
      until sy <> comma;
      if sy <> rparent then
        error(4);
      insymbol;
      if sy <> semicolon then
        error(14)
    end;
    if sy = semicolon then
      insymbol
  end
  else
    error(3);
  repeat
    block(fsys, period, nil);
    if sy <> period then
      error(21)
  until (sy = period) or Eof(prd);
  if list then
    Writeln(Output);
  if errinx <> 0 then
  begin
    list := False;
    endofline
  end;
end { programme };

procedure stdnames;
begin
  { 'mark' and 'release' were removed and replaced with placeholders }
    { 'mark' and 'release' were removed and replaced with placeholders }
  na[ 1] := 'false    '; na[ 2] := 'true     '; na[ 3] := 'input    ';
  na[ 4] := 'output   '; na[ 5] := 'get      '; na[ 6] := 'put      ';
  na[ 7] := 'reset    '; na[ 8] := 'rewrite  '; na[ 9] := 'read     ';
  na[10] := 'write    '; na[11] := 'pack     '; na[12] := 'unpack   ';
  na[13] := 'new      '; na[14] := '---      '; na[15] := 'readln   ';
  na[16] := 'writeln  ';
  na[17] := 'abs      '; na[18] := 'sqr      '; na[19] := 'trunc    ';
  na[20] := 'odd      '; na[21] := 'ord      '; na[22] := 'chr      ';
  na[23] := 'pred     '; na[24] := 'succ     '; na[25] := 'eof      ';
  na[26] := 'eoln     ';
  na[27] := 'sin      '; na[28] := 'cos      '; na[29] := 'exp      ';
  na[30] := 'sqrt     '; na[31] := 'ln       '; na[32] := 'arctan   ';
  na[33] := 'prd      '; na[34] := 'prr      '; na[35] := '---      ';
  na[36] := 'maxint   '; na[37] := 'round    '; na[38] := 'page     ';
  na[39] := 'dispose  ';
end { stdnames };

procedure enterstdtypes;
begin
                                                        { type underlying: }
                                                        { **************** }

  New(intptr);
  pshstc(intptr);                              { Integer }
  with intptr^ do
  begin
    size := intsize;
    form := scalar;
    scalkind := standard;
    packing := False
  end;
  New(realptr);
  pshstc(realptr);                             { real }
  with realptr^ do
  begin
    size := realsize;
    form := scalar;
    scalkind := standard;
    packing := False
  end;
  New(charptr);
  pshstc(charptr);                             { Char }
  with charptr^ do
  begin
    size := charsize;
    form := scalar;
    scalkind := standard;
    packing := False
  end;
  New(boolptr);
  pshstc(boolptr);                             { Boolean }
  with boolptr^ do
  begin
    size := boolsize;
    form := scalar;
    scalkind := declared;
    packing := False
  end;
  New(nilptr);
  pshstc(nilptr);                              { nil }
  with nilptr^ do
  begin
    eltype := nil;
    size := ptrsize;
    form := pointer;
    packing := False
  end;
  { for alignment of parameters }
  New(parmptr);
  pshstc(parmptr);
  with parmptr^ do
  begin
    size := parmsize;
    form := scalar;
    scalkind := standard;
    packing := False
  end;
  New(textptr);
  pshstc(textptr);                             { text }
  with textptr^ do
  begin
    filtype := charptr;
    size := filesize + charsize;
    form := files;
    packing := False
  end
end { enterstdtypes };

procedure entstdnames;
var
  cp, cp1: ctp;
  i: Integer;
begin
                                                        { name: }
                                                        { ***** }

  New(cp);
  ininam(cp);                                  { Integer }
  with cp^ do
  begin
    strassvr(name, 'integer  ');
    idtype := intptr;
    klass := types
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { real }
  with cp^ do
  begin
    strassvr(name, 'real     ');
    idtype := realptr;
    klass := types
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { Char }
  with cp^ do
  begin
    strassvr(name, 'char     ');
    idtype := charptr;
    klass := types
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { Boolean }
  with cp^ do
  begin
    strassvr(name, 'boolean  ');
    idtype := boolptr;
    klass := types
  end;
  usclrptr := cp; { save to satisfy broken tags }
  enterid(cp);
  New(cp);
  ininam(cp);                                  { text }
  with cp^ do
  begin
    strassvr(name, 'text     ');
    idtype := textptr;
    klass := types
  end;
  enterid(cp);
  cp1 := nil;
  for i := 1 to 2 do
  begin
    New(cp);
    ininam(cp);                                { False,True }
    with cp^ do
    begin
      strassvr(name, na[i]);
      idtype := boolptr;
      next := cp1;
      values.ival := i - 1;
      klass := konst
    end;
    enterid(cp);
    cp1 := cp
  end;
  boolptr^.fconst := cp;
  for i := 3 to 4 do
  begin
    New(cp);
    ininam(cp);                                { input,Output }
    with cp^ do
    begin
      strassvr(name, na[i]);
      idtype := textptr;
      klass := vars;
      vkind := actual;
      next := nil;
      vlev := 1;
      vaddr := gc;
      gc := gc + filesize + charsize; { files are global now }
      threat := False;
      forcnt := 0
    end;
    enterid(cp);
    if i = 3 then
      inputptr := cp
    else
      outputptr := cp
  end;
  for i := 33 to 34 do
  begin
    New(cp);
    ininam(cp);                                { prd,prr files }
    with cp^ do
    begin
      strassvr(name, na[i]);
      idtype := textptr;
      klass := vars;
      vkind := actual;
      next := nil;
      vlev := 1;
      vaddr := gc;
      gc := gc + filesize + charsize; { alloc global file }
      threat := False;
      forcnt := 0
    end;
    enterid(cp)
  end;
  for i := 5 to 16 do
    if i <> 14 then { no longer doing release }
    begin
      New(cp);
      ininam(cp);                              { get,put,reset }
      with cp^ do                              { rewrite,Read }
      begin
        strassvr(name, na[i]);
        idtype := nil;                         { Write,pack }
        pflist := nil;
        next := nil;
        key := i - 4;                          { unpack,New }
        klass := proc;
        pfdeckind := standard                  { readln,Writeln }
      end;
      enterid(cp)
    end;
  for i := 17 to 26 do
  begin
    New(cp);
    ininam(cp);                                { abs,sqr,trunc }
    with cp^ do                                { odd,Ord,chr }
    begin
      strassvr(name, na[i]);
      idtype := nil;                           { pred,succ,Eof }
      pflist := nil;
      next := nil;
      key := i - 16;
      klass := func;
      pfdeckind := standard
    end;
    enterid(cp)
  end;
  for i := 27 to 32 do
  begin
    New(cp);
    ininam(cp); { parameter of predeclared functions }
    with cp^ do
    begin
      strassvr(name, '         ');
      idtype := realptr;
      klass := vars;
      vkind := actual;
      next := nil;
      vlev := 1;
      vaddr := 0;
      threat := False;
      forcnt := 0
    end;
    New(cp1);
    ininam(cp1);                               { sin,cos,exp }
    with cp1^ do                               { sqrt,ln,arctan }
    begin
      strassvr(name, na[i]);
      idtype := realptr;
      pflist := cp;
      forwdecl := False;
      externl := True;
      pflev := 0;
      pfname := i - 12;
      klass := func;
      pfdeckind := declared;
      pfkind := actual
    end;
    enterid(cp1)
  end;
  New(cp);
  ininam(cp);                                  { maxint }
  with cp^ do
  begin
    strassvr(name, na[36]);
    idtype := intptr;
    next := nil;
    values.ival := maxint;
    klass := konst
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { round }
  with cp^ do
  begin
    strassvr(name, na[37]);
    idtype := nil;
    pflist := nil;
    next := nil;
    key := 16;
    klass := func;
    pfdeckind := standard
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { page }
  with cp^ do
  begin
    strassvr(name, na[38]);
    idtype := nil;
    pflist := nil;
    next := nil;
    key := 17;
    klass := proc;
    pfdeckind := standard
  end;
  enterid(cp);
  New(cp);
  ininam(cp);                                  { Dispose }
  with cp^ do
  begin
    strassvr(name, na[39]);
    idtype := nil;
    pflist := nil;
    next := nil;
    key := 18;
    klass := proc;
    pfdeckind := standard
  end;
  enterid(cp)
end { entstdnames };

procedure enterundecl;
begin
  New(utypptr);
  ininam(utypptr);
  with utypptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    klass := types
  end;
  New(ucstptr);
  ininam(ucstptr);
  with ucstptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    next := nil;
    klass := konst;
    values.ival := 0
  end;
  New(uvarptr);
  ininam(uvarptr);
  with uvarptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    vkind := actual;
    next := nil;
    vlev := 0;
    vaddr := 0;
    klass := vars;
    threat := False;
    forcnt := 0
  end;
  New(ufldptr);
  ininam(ufldptr);
  with ufldptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    next := nil;
    fldaddr := 0;
    klass := field
  end;
  New(uprcptr);
  ininam(uprcptr);
  with uprcptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    forwdecl := False;
    next := nil;
    externl := False;
    pflev := 0;
    genlabel(pfname);
    klass := proc;
    pflist := nil;
    pfdeckind := declared;
    pfkind := actual
  end;
  New(ufctptr);
  ininam(ufctptr);
  with ufctptr^ do
  begin
    strassvr(name, '         ');
    idtype := nil;
    next := nil;
    forwdecl := False;
    externl := False;
    pflev := 0;
    genlabel(pfname);
    klass := func;
    pflist := nil;
    pfdeckind := declared;
    pfkind := actual
  end
end { enterundecl };

{ tear down storage allocations from enterundecl }

procedure exitundecl;
begin
  putnam(utypptr);
  putnam(ucstptr);
  putnam(uvarptr);
  putnam(ufldptr);
  putnam(uprcptr);
  putnam(ufctptr);
end { exitundecl };

procedure initscalars;
var
  i: Integer;
  c: Char;
begin
  fwptr := nil;
  for c := 'a' to 'z' do
    option[c] := False;
  prtables := False;  option['t'] := False;
  list     := True;   option['l'] := True;
  prcode   := True;   option['c'] := True;
  debug    := True;   option['d'] := True;
  chkvar   := True;   option['v'] := True;
  chkref   := True;   option['r'] := True;
  chkudtc  := True;   option['u'] := True;
  dp := True;
  errinx := 0;
  intlabel := 0;
  kk := maxids;
  fextfilep := nil;
  lc := lcaftermarkstack;
  gc := 0;
  {  note in the above reservation of buffer store for 2 text files  }
  ic := 3;
  eol := True;
  linecount := 0;
  ch := ' ';
  chcnt := 0;
  mxint10 := maxint div 10;
  inputhdf := False; { set 'input' not in header files }
  outputhdf := False; { set 'output' not in header files }
  for i := 1 to 500 do
    errtbl[i] := False; { initialize error tracking }
  toterr := 0; { clear error count }
  { clear the recycling tracking counters }
  strcnt := 0; { strings }
  cspcnt := 0; { constants }
  stpcnt := 0; { structures }
  ctpcnt := 0; { identifiers }
  lbpcnt := 0; { label counts }
  filcnt := 0; { file tracking counts }
  cipcnt := 0 { case entry tracking counts }
end { initscalars };

procedure initsets;
begin
  constbegsys := [addop, intconst, realconst, stringconst, ident];
  simptypebegsys := [lparent] + constbegsys;
  typebegsys := [arrow, packedsy, arraysy, recordsy, setsy, filesy] + simptypebegsys;
  typedels := [arraysy, recordsy, setsy, filesy];
  blockbegsys := [labelsy, constsy, typesy, varsy, procsy, funcsy, beginsy];
  selectsys := [arrow, period, lbrack];
  facbegsys := [intconst, realconst, stringconst, ident, lparent, lbrack, notsy, nilsy];
  statbegsys := [beginsy, gotosy, ifsy, whilesy, repeatsy, forsy, withsy, casesy];
end { initsets };

procedure inittables;
  procedure reswords;
  begin
    rw[ 1] := 'if       '; rw[ 2] := 'do       '; rw[ 3] := 'of       ';
    rw[ 4] := 'to       '; rw[ 5] := 'in       '; rw[ 6] := 'or       ';
    rw[ 7] := 'end      '; rw[ 8] := 'for      '; rw[ 9] := 'var      ';
    rw[10] := 'div      '; rw[11] := 'mod      '; rw[12] := 'set      ';
    rw[13] := 'and      '; rw[14] := 'not      '; rw[15] := 'nil      ';
    rw[16] := 'then     '; rw[17] := 'else     '; rw[18] := 'with     ';
    rw[19] := 'goto     '; rw[20] := 'case     '; rw[21] := 'type     ';
    rw[22] := 'file     '; rw[23] := 'begin    '; rw[24] := 'until    ';
    rw[25] := 'while    '; rw[26] := 'array    '; rw[27] := 'const    ';
    rw[28] := 'label    '; rw[29] := 'repeat   '; rw[30] := 'record   ';
    rw[31] := 'downto   '; rw[32] := 'packed   '; rw[33] := 'program  ';
    rw[34] := 'function '; rw[35] := 'procedure';
    frw[1] :=  1; frw[2] :=  1; frw[3] :=  7; frw[4] := 16; frw[5] := 23;
    frw[6] := 29; frw[7] := 33; frw[8] := 34; frw[9] := 35; frw[10] := 36;
  end { reswords };

  procedure symbols;
  begin
    rsy[ 1] := ifsy;      rsy[ 2] := dosy;      rsy[ 3] := ofsy;
    rsy[ 4] := tosy;      rsy[ 5] := relop;     rsy[ 6] := addop;
    rsy[ 7] := endsy;     rsy[ 8] := forsy;     rsy[ 9] := varsy;
    rsy[10] := mulop;     rsy[11] := mulop;     rsy[12] := setsy;
    rsy[13] := mulop;     rsy[14] := notsy;     rsy[15] := nilsy;
    rsy[16] := thensy;    rsy[17] := elsesy;    rsy[18] := withsy;
    rsy[19] := gotosy;    rsy[20] := casesy;    rsy[21] := typesy;
    rsy[22] := filesy;    rsy[23] := beginsy;   rsy[24] := untilsy;
    rsy[25] := whilesy;   rsy[26] := arraysy;   rsy[27] := constsy;
    rsy[28] := labelsy;   rsy[29] := repeatsy;  rsy[30] := recordsy;
    rsy[31] := downtosy;  rsy[32] := packedsy;  rsy[33] := progsy;
    rsy[34] := funcsy;    rsy[35] := procsy;
    ssy['+'] := addop;    ssy['-'] := addop;    ssy['*'] := mulop;
    ssy['/'] := mulop;    ssy['('] := lparent;  ssy[')'] := rparent;
    ssy['$'] := othersy;  ssy['='] := relop;    ssy[' '] := othersy;
    ssy[','] := comma;    ssy['.'] := period;   ssy['''']:= othersy;
    ssy['['] := lbrack;   ssy[']'] := rbrack;   ssy[':'] := colon;
    ssy['^'] := arrow;    ssy['<'] := relop;    ssy['>'] := relop;
    ssy[';'] := semicolon; ssy['@'] := arrow;
  end { symbols };

  procedure rators;
  var
    i: Integer;
  begin
    for i := 1 to maxres { nr of res words } do
      rop[i] := noop;
    rop[5] := inop; rop[10] := idiv; rop[11] := imod;
    rop[6] := orop; rop[13] := andop;
    for i := ordminchar to ordmaxchar do
      sop[chr(i)] := noop;
    sop['+'] := plus; sop['-'] := minus; sop['*'] := mul; sop['/'] := rdiv;
    sop['='] := eqop; sop['<'] := ltop;  sop['>'] := gtop;
  end { rators };

  procedure procmnemonics;
  begin
    { There are two mnemonics that have no counterpart in the
      assembler/interpreter: wro, pak. I didn't find a generator for them, and
      suspect they are abandoned. }
    sna[ 1] :=' get'; sna[ 2] :=' put'; sna[ 3] :=' rdi'; sna[ 4] :=' rdr';
    sna[ 5] :=' rdc'; sna[ 6] :=' wri'; sna[ 7] :=' wro'; sna[ 8] :=' wrr';
    sna[ 9] :=' wrc'; sna[10] :=' wrs'; sna[11] :=' pak'; sna[12] :=' new';
    sna[13] :=' rst'; sna[14] :=' eln'; sna[15] :=' sin'; sna[16] :=' cos';
    sna[17] :=' exp'; sna[18] :=' sqt'; sna[19] :=' log'; sna[20] :=' atn';
    sna[21] :=' rln'; sna[22] :=' wln'; sna[23] :=' sav';
    { New procedure/function memonics for p5 }
    sna[24] :=' pag'; sna[25] :=' rsf'; sna[26] :=' rwf'; sna[27] :=' wrb';
    sna[28] :=' wrf'; sna[29] :=' dsp'; sna[30] :=' wbf'; sna[31] :=' wbi';
    sna[32] :=' wbr'; sna[33] :=' wbc'; sna[34] :=' wbb'; sna[35] :=' rbf';
    sna[36] :=' rsb'; sna[37] :=' rwb'; sna[38] :=' gbf'; sna[39] :=' pbf';
    sna[40] :=' rib'; sna[41] :=' rcb'; sna[42] :=' nwl'; sna[43] :=' dsl';
    sna[44] :=' eof'; sna[45] :=' efb'; sna[46] :=' fbv'; sna[47] :=' fvb';
    sna[48] :=' wbx';

  end { procmnemonics };

  procedure instrmnemonics;
  begin
    { ??? memnemonics are placeholders }
    mn[ 0] :=' abi'; mn[ 1] :=' abr'; mn[ 2] :=' adi'; mn[ 3] :=' adr';
    mn[ 4] :=' and'; mn[ 5] :=' dif'; mn[ 6] :=' dvi'; mn[ 7] :=' dvr';
    mn[ 8] :=' ???'; mn[ 9] :=' flo'; mn[10] :=' flt'; mn[11] :=' inn';
    mn[12] :=' int'; mn[13] :=' ior'; mn[14] :=' mod'; mn[15] :=' mpi';
    mn[16] :=' mpr'; mn[17] :=' ngi'; mn[18] :=' ngr'; mn[19] :=' not';
    mn[20] :=' odd'; mn[21] :=' sbi'; mn[22] :=' sbr'; mn[23] :=' sgs';
    mn[24] :=' sqi'; mn[25] :=' sqr'; mn[26] :=' sto'; mn[27] :=' trc';
    mn[28] :=' uni'; mn[29] :=' stp'; mn[30] :=' csp'; mn[31] :=' dec';
    mn[32] :=' ent'; mn[33] :=' fjp'; mn[34] :=' inc'; mn[35] :=' ind';
    mn[36] :=' ixa'; mn[37] :=' lao'; mn[38] :=' lca'; mn[39] :=' ldo';
    mn[40] :=' mov'; mn[41] :=' mst'; mn[42] :=' ret'; mn[43] :=' sro';
    mn[44] :=' xjp'; mn[45] :=' chk'; mn[46] :=' cup'; mn[47] :=' equ';
    mn[48] :=' geq'; mn[49] :=' grt'; mn[50] :=' lda'; mn[51] :=' ldc';
    mn[52] :=' leq'; mn[53] :=' les'; mn[54] :=' lod'; mn[55] :=' neq';
    mn[56] :=' str'; mn[57] :=' ujp'; mn[58] :=' ord'; mn[59] :=' chr';
    mn[60] :=' ujc';
    { new instruction memonics for p5 }
    mn[61] :=' rnd'; mn[62] :=' pck'; mn[63] :=' upk'; mn[64] :=' rgs';
    mn[65] :=' ???'; mn[66] :=' ipj'; mn[67] :=' cip'; mn[68] :=' lpa';
    mn[69] :=' ???'; mn[70] :=' ???'; mn[71] :=' dmp'; mn[72] :=' swp';
    mn[73] :=' tjp'; mn[74] :=' lip'; mn[75] :=' ckv'; mn[76] :=' dup';
    mn[77] :=' cke'; mn[78] :=' cks'; mn[79] :=' inv'; mn[80] :=' ckl';
    mn[81] :=' cta'; mn[82] :=' ivt';
  end { instrmnemonics };

  procedure chartypes;
  var
    i: Integer;
  begin
    for i := ordminchar to ordmaxchar do
      chartp[chr(i)] := illegal;
    chartp['a'] := letter  ;
    chartp['b'] := letter  ; chartp['c'] := letter  ;
    chartp['d'] := letter  ; chartp['e'] := letter  ;
    chartp['f'] := letter  ; chartp['g'] := letter  ;
    chartp['h'] := letter  ; chartp['i'] := letter  ;
    chartp['j'] := letter  ; chartp['k'] := letter  ;
    chartp['l'] := letter  ; chartp['m'] := letter  ;
    chartp['n'] := letter  ; chartp['o'] := letter  ;
    chartp['p'] := letter  ; chartp['q'] := letter  ;
    chartp['r'] := letter  ; chartp['s'] := letter  ;
    chartp['t'] := letter  ; chartp['u'] := letter  ;
    chartp['v'] := letter  ; chartp['w'] := letter  ;
    chartp['x'] := letter  ; chartp['y'] := letter  ;
    chartp['z'] := letter  ;
    chartp['A'] := letter  ;
    chartp['B'] := letter  ; chartp['C'] := letter  ;
    chartp['D'] := letter  ; chartp['E'] := letter  ;
    chartp['F'] := letter  ; chartp['G'] := letter  ;
    chartp['H'] := letter  ; chartp['I'] := letter  ;
    chartp['J'] := letter  ; chartp['K'] := letter  ;
    chartp['L'] := letter  ; chartp['M'] := letter  ;
    chartp['N'] := letter  ; chartp['O'] := letter  ;
    chartp['P'] := letter  ; chartp['Q'] := letter  ;
    chartp['R'] := letter  ; chartp['S'] := letter  ;
    chartp['T'] := letter  ; chartp['U'] := letter  ;
    chartp['V'] := letter  ; chartp['W'] := letter  ;
    chartp['X'] := letter  ; chartp['Y'] := letter  ;
    chartp['Z'] := letter  ;
    chartp['0'] := number  ;
    chartp['1'] := number  ; chartp['2'] := number  ;
    chartp['3'] := number  ; chartp['4'] := number  ;
    chartp['5'] := number  ; chartp['6'] := number  ;
    chartp['7'] := number  ; chartp['8'] := number  ;
    chartp['9'] := number  ; chartp['+'] := special ;
    chartp['-'] := special ; chartp['*'] := special ;
    chartp['/'] := special ; chartp['('] := chlparen;
    chartp[')'] := special ; chartp['$'] := special ;
    chartp['='] := special ; chartp[' '] := chspace ;
    chartp[','] := special ; chartp['.'] := chperiod;
    chartp['''']:= chstrquo; chartp['['] := special ;
    chartp[']'] := special ; chartp[':'] := chcolon ;
    chartp['^'] := special ; chartp[';'] := special ;
    chartp['<'] := chlt    ; chartp['>'] := chgt    ;
    chartp['{'] := chlcmt  ; chartp['}'] := special ;
    chartp['@'] := special ;

    ordint['0'] := 0; ordint['1'] := 1; ordint['2'] := 2;
    ordint['3'] := 3; ordint['4'] := 4; ordint['5'] := 5;
    ordint['6'] := 6; ordint['7'] := 7; ordint['8'] := 8;
    ordint['9'] := 9;
  end;

  procedure initdx;
  begin
    { [sam] if your sizes are not even multiples of
      stackelsize, you are going to need to compensate this.
      entries marked with * go to secondary table }
    cdx[ 0] :=  0;                   cdx[ 1] :=  0;
    cdx[ 2] := +intsize;             cdx[ 3] := +realsize;
    cdx[ 4] := +intsize;             cdx[ 5] := +setsize;
    cdx[ 6] := +intsize;             cdx[ 7] := +realsize;
    cdx[ 8] :=  0;                   cdx[ 9] := +intsize-realsize;
    cdx[10] :=  -realsize+intsize;   cdx[11] := +setsize;
    cdx[12] := +setsize;             cdx[13] := +intsize;
    cdx[14] := +intsize;             cdx[15] := +intsize;
    cdx[16] := +realsize;            cdx[17] :=  0;
    cdx[18] :=  0;                   cdx[19] :=  0;
    cdx[20] :=  0;                   cdx[21] := +intsize;
    cdx[22] := +realsize;            cdx[23] := +intsize-setsize;
    cdx[24] :=  0;                   cdx[25] :=  0;
    cdx[26] := 1{*};                 cdx[27] := +realsize-intsize;
    cdx[28] := +setsize;             cdx[29] :=  0;
    cdx[30] :=  0;                   cdx[31] :=  2{*};
    cdx[32] :=  0;                   cdx[33] := +intsize;
    cdx[34] :=  2{*};                cdx[35] :=  3{*};
    cdx[36] := +intsize;             cdx[37] := -adrsize;
    cdx[38] := -adrsize;             cdx[39] :=  4{*};
    cdx[40] := +adrsize*2;           cdx[41] :=  0;
    cdx[42] :=  2{*};                cdx[43] :=  5{*};
    cdx[44] := +intsize;             cdx[45] :=  2{*};
    cdx[46] :=  0;                   cdx[47] :=  6{*};
    cdx[48] :=  6{*};                cdx[49] :=  6{*};
    cdx[50] := -adrsize;             cdx[51] :=  4{*};
    cdx[52] :=  6{*};                cdx[53] :=  6{*};
    cdx[54] :=  4{*};                cdx[55] :=  6{*};
    cdx[56] :=  5{*};                cdx[57] :=  0;
    cdx[58] :=  2{*};                cdx[59] :=  0;
    cdx[60] :=  0;                   cdx[61] :=  +realsize-intsize;
    cdx[62] := +adrsize*3;           cdx[63] := +adrsize*3;
    cdx[64] := +intsize*2-setsize;   cdx[65] :=  0;
    cdx[66] :=  0;                   cdx[67] := +ptrsize;
    cdx[68] := -adrsize*2;           cdx[69] :=  0;
    cdx[70] :=  0;                   cdx[71] := +ptrsize;
    cdx[72] :=  0;                   cdx[73] := +intsize;
    cdx[74] := -adrsize*2;           cdx[75] :=  2{*};
    cdx[76] :=  4{*};                cdx[77] :=  +intsize*2;
    cdx[78] := -intsize;             cdx[79] :=  +adrsize;
    cdx[80] :=  0;                   cdx[81] :=  0;
    cdx[82] :=  0;

    { secondary table order is i, r, b, c, a, s, m }
    cdxs[1][1] := +(adrsize+intsize);  { stoi }
    cdxs[1][2] := +(adrsize+realsize); { stor }
    cdxs[1][3] := +(adrsize+intsize);  { stob }
    cdxs[1][4] := +(adrsize+intsize);  { stoc }
    cdxs[1][5] := +(adrsize+adrsize);  { stoa }
    cdxs[1][6] := +(adrsize+setsize);  { stos }
    cdxs[1][7] := 0;

    cdxs[2][1] := 0; { deci/inci/ordi/chki/reti }
    cdxs[2][2] := 0; { chkr/retr }
    cdxs[2][3] := 0; { decb/incb/ordb/chkb/retb }
    cdxs[2][4] := 0; { decc/incc/ordc/chkc/retc }
    cdxs[2][5] := 0; { chka/reta }
    cdxs[2][6] := 0; { chks }
    cdxs[2][7] := 0;

    cdxs[3][1] := +adrsize-intsize;  { indi }
    cdxs[3][2] := +adrsize-realsize; { indr }
    cdxs[3][3] := +adrsize-intsize;  { indb }
    cdxs[3][4] := +adrsize-intsize;  { indc }
    cdxs[3][5] := +adrsize-adrsize;  { inda }
    cdxs[3][6] := +adrsize-setsize;  { inds }
    cdxs[3][7] := 0;

    cdxs[4][1] := -intsize;  { ldoi/ldc/lodi/dupi }
    cdxs[4][2] := -realsize; { ldor/ldc/lodr/dupr }
    cdxs[4][3] := -intsize;  { ldob/ldc/lodb/dupb }
    cdxs[4][4] := -intsize;  { ldoc/ldc/lodc/dupc }
    cdxs[4][5] := -adrsize;  { ldoa/ldc/loda/dupa }
    cdxs[4][6] := -setsize;  { ldos/ldc/lods/dups }
    cdxs[4][7] := 0;

    cdxs[5][1] := +intsize;  { sroi/stri }
    cdxs[5][2] := +realsize; { sror/strr }
    cdxs[5][3] := +intsize;  { srob/strb }
    cdxs[5][4] := +intsize;  { sroc/strc }
    cdxs[5][5] := +adrsize;  { sroa/stra }
    cdxs[5][6] := +setsize;  { sros/strs }
    cdxs[5][7] := 0;

    { note that all of the comparisions share the same table }
    cdxs[6][1] := +(intsize+intsize)-intsize; { equi/neqi/geqi/grti/leqi/lesi }
    cdxs[6][2] := +(realsize+realsize)-intsize; { equr/neqr/geqr/grtr/leqr/lesr }
    cdxs[6][3] := +(intsize+intsize)-intsize; { equb/neqb/geqb/grtb/leqb/lesb }
    cdxs[6][4] := +(intsize+intsize)-intsize; { equc/neqc/geqc/grtc/leqc/lesc }
    cdxs[6][5] := +(adrsize+intsize)-adrsize; { equa/neqa/geqa/grta/leqa/lesa }
    cdxs[6][6] := +(setsize+setsize)-intsize; { equs/neqs/geqs/grts/leqs/less }
    cdxs[6][7] := +(adrsize+adrsize)-intsize; { equm/neqm/geqm/grtm/leqm/lesm }

    pdx[ 1] := +adrsize;             pdx[ 2] := +adrsize;
    pdx[ 3] := +adrsize;             pdx[ 4] := +adrsize;
    pdx[ 5] := +adrsize;             pdx[ 6] := +adrsize*2;
    pdx[ 7] := 0;                    pdx[ 8] := +(realsize+intsize);
    pdx[ 9] := +intsize*2;           pdx[10] := +(adrsize+intsize*2);
    pdx[11] :=  0;                   pdx[12] := +ptrsize*2;
    pdx[13] :=  0;                   pdx[14] := +adrsize-intsize;
    pdx[15] :=  0;                   pdx[16] :=  0;
    pdx[17] :=  0;                   pdx[18] :=  0;
    pdx[19] :=  0;                   pdx[20] :=  0;
    pdx[21] :=  0;                   pdx[22] :=  0;
    pdx[23] :=  0;                   pdx[24] := +adrsize;
    pdx[25] := +adrsize;             pdx[26] := +adrsize;
    pdx[27] := +intsize*2;           pdx[28] := +(realsize+intsize*2);
    pdx[29] := +adrsize*2;           pdx[30] := +(adrsize+intsize);
    pdx[31] := +intsize;             pdx[32] := +realsize;
    pdx[33] := +intsize;             pdx[34] := +intsize;
    pdx[35] := +(intsize+adrsize);   pdx[36] := +adrsize;
    pdx[37] := +adrsize;             pdx[38] := +(intsize+adrsize);
    pdx[39] := +(intsize+adrsize);   pdx[40] := +(adrsize+intsize*2);
    pdx[41] := +(adrsize+intsize*2); pdx[42] := +(adrsize+intsize*2);
    pdx[43] := +(adrsize+intsize*2); pdx[44] := +adrsize-intsize;
    pdx[45] := +adrsize-intsize;     pdx[46] :=  0;
    pdx[47] := +intsize;             pdx[48] := +intsize;
  end;

begin { inittables }
  reswords;
  symbols;
  rators;
  instrmnemonics;
  procmnemonics;
  chartypes;
  initdx;
end { inittables };

begin
  if ParamCount > 0 then
  begin
    SrcFile := ParamStr(ParamCount);
    DstFile := ChangeFileExt(SrcFile, '.p5');
  end
  else
  begin
    SrcFile := 'prd';
    DstFile := 'prr';
  end;

  Write('P5 Pascal compiler vs. ', majorver: 1, '.', minorver: 1);
  if experiment then
    Write('.x');
  Write(' (Built with Delphi)');
  Writeln;
  Writeln('Pascal-P5 complies with the requirements of level 0 of ISO/IEC 7185.');
  Writeln;

  if (not TFile.Exists(SrcFile)) or
    FindCmdLineSwitch('?', ['-', '/'], True) or
    FindCmdLineSwitch('-help', ['-'], True) then
    begin
      Writeln('PCOM [+T | -T] [+L | -L] [+D | -D] [+C | -C] [filename]');
      Writeln;
      Writeln(' +   Turn on the option.');
      Writeln(' -   Turn off the option.');
      Writeln(' T   Print internal tables after each routine is compiled. (Default: Off)');
      Writeln(' L   List the source program during compilation. (Default: On)');
      Writeln(' D   Add extra code to check array bounds, subranges, etc. (Default: On)');
      Writeln(' C   Output intermediate code. (Default: On)');
      Exit;
    end;

  AssignFile(prd, SrcFile);
  AssignFile(prr, DstFile);
  try
    { initialize }
    { ********** }
    initscalars;
    initsets;
    inittables;

    { enter standard names and standard types: }
    { **************************************** }
    level := 0;
    top := 0;
    with display[0] do
    begin
      fname := nil;
      flabel := nil;
      fconst := nil;
      fstruct := nil;
      packing := False;
      occur := blck;
      bname := nil
    end;
    enterstdtypes;
    stdnames;
    entstdnames;
    enterundecl;
    top := 1;
    level := 1;
    with display[1] do
    begin
      fname := nil;
      flabel := nil;
      fconst := nil;
      fstruct := nil;
      packing := False;
      occur := blck;
      bname := nil
    end;

    { compile: }
    { ******** }

    Reset(prd);
    Rewrite(prr); { open Output file }

    if FindCmdLineSwitch('T', ['+'], True) then
      prtables := True;
    if FindCmdLineSwitch('T', ['-'], True) then
      prtables := False;
    if FindCmdLineSwitch('L', ['+'], True) then
      list := True;
    if FindCmdLineSwitch('L', ['-'], True) then
      list := False;
    if FindCmdLineSwitch('D', ['+'], True) then
      debug := True;
    if FindCmdLineSwitch('D', ['-'], True) then
      debug := False;
    if FindCmdLineSwitch('C', ['+'], True) then
      prcode := True;
    if FindCmdLineSwitch('C', ['-'], True) then
      prcode := False;

    if prcode then
      begin
        { Write generator comment }
        Writeln(prr, 'i');
        Writeln(prr,
          'i Pascal intermediate file Generated by P5 Pascal compiler vs. ',
          majorver: 1, '.', minorver: 1);
        Writeln(prr, 'i');

        { Write initial option values }
        Write(prr, 'o ');
        for c := 'a' to 'z' do
        begin
          Write(prr, c);
          if option[c] then
            Write(prr, '+')
          else
            Write(prr, '-')
        end;
        Writeln(prr);
      end;

    insymbol;
    programme(blockbegsys + statbegsys - [casesy]);

    { Dispose of levels 0 and 1 }
    putdsp(1);
    putdsp(0);

    { remove undeclared ids }
    exitundecl;

    Writeln;
    Writeln('Errors in program: ', toterr: 1);
    { Output error report as required }
    f := True;
    for i := 1 to 500 do
      if errtbl[i] then
      begin
        if f then
        begin
          Writeln;
          Writeln('Error numbers in listing:');
          Writeln('-------------------------');
          f := False
        end;
        Write(i: 3, '  ');
        errmsg(i);
        Writeln
      end;
    if not f then
      Writeln;

    if doprtryc then
    begin { print recyling tracking counts }
      Writeln;
      Writeln('Recycling tracking counts:');
      Writeln;
      Writeln('string quants:              ', strcnt: 1);
      Writeln('constants:                  ', cspcnt: 1);
      Writeln('structures:                 ', stpcnt: 1);
      Writeln('identifiers:                ', ctpcnt: 1);
      Writeln('label counts:               ', lbpcnt: 1);
      Writeln('file tracking counts:       ', filcnt: 1);
      Writeln('case entry tracking counts: ', cipcnt: 1);
      Writeln;
    end;

    if doprtlab then
      prtlabels; { dump labels}
    if dodmpdsp then
      prtdsp; { dump display }

    { perform errors for recycling balance }

    if strcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'string recycle balance: ', strcnt: 1);
    if cspcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'constant recycle balance: ', cspcnt: 1);
    if stpcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'structure recycle balance: ', stpcnt: 1);
    if ctpcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'identifier recycle balance: ', ctpcnt: 1);
    if lbpcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'label recycle balance: ', lbpcnt: 1);
    if filcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'file recycle balance: ', filcnt: 1);
    if cipcnt <> 0 then
      Writeln(ERROR_HEADER,  ': ', 'case recycle balance: ', cipcnt: 1);
  except
    on E: EAbort do
      ;
  end;

  CloseFile(prd);
  Flush(prr);
  CloseFile(prr);
end.

