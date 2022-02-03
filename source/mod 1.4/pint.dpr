{*******************************************************************************
*                                                                              *
*                           Portable Pascal compiler                           *
*                           ************************                           *
*                                                                              *
*                                 Pascal P5                                    *
*                                                                              *
*                                 ETH May 76                                   *
*                                                                              *
* Authors:                                                                     *
*                                                                              *
*    Urs Ammann                                                                *
*    Kesav Nori                                                                *
*    Christian Jacobi                                                          *
*    K. Jensen                                                                 *
*    N. Wirth                                                                  *
*                                                                              *
* Address:                                                                     *
*                                                                              *
*    Institut Fuer Informatik                                                  *
*    Eidg. Technische Hochschule                                               *
*    CH-8096 Zuerich                                                           *
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
* Note for the implementation.                                                 *
* ===========================                                                  *
* This interpreter is written for the case where all the fundamental types     *
* take one storage unit.                                                       *
*                                                                              *
* In an actual implementation, the handling of the sp pointer has to take      *
* into account the fact that the types may have lengths different from one:    *
* in push and pop operations the sp has to be increased and decreased not      *
* by 1, but by a number depending on the type concerned.                       *
*                                                                              *
* However, where the number of units of storage has been computed by the       *
* compiler, the value must not be corrected, since the lengths of the types    *
* involved have already been taken into account.                               *
*                                                                              *
* P5 errors added:                                                             *
*                                                                              *
* 182 identifier too long                                                      *
* 183 For index variable must be local to this block                           *
* 184 Interprocedure goto does not reference outter block of destination       *
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
* not represent files as fully expressed variables, such as within an array    *
* or record, and were effectively treated as constants. To treat them as True  *
* variable accesses, the stacking order of the file in all file subroutines    *
* was changed so that the file is on the bottom. This matches the source       *
* order of the file in Write(f, ...) or Read(f, ...). Also, the file           *
* operations now leave the file on the stack for the duration of a Write or    *
* Read, then dump them using a specific new instruction "dmp". This allows     *
* multiparameter writes and reads to be effectively a chain of single          *
* operations using one file reference. Finally, files were tied to the type    *
* ending 'a', because files are now full variable references.                  *
*                                                                              *
* New layout of memory in store:                                               *
*                                                                              *
*    maxstr ->    ---------------------                                        *
*                 | Constants         |                                        *
*        cp ->    ---------------------                                        *
*                 | Stack             |                                        *
*        sp ->    ---------------------                                        *
*                 | Free space        |                                        *
*        np ->    ---------------------                                        *
*                 | Heap              |                                        *
*        gbtop -> ---------------------                                        *
*                 | Globals           |                                        *
*        pctop -> ---------------------                                        *
*                 | Code              |                                        *
*                 ---------------------                                        *
*                                                                              *
* The constants are loaded upside down from the top of memory. The heap grows  *
* down, the stack grows up, and when they cross, it is an overflow error.      *
*                                                                              *
*******************************************************************************}

{ Set default configuration flags. This gives proper behavior even if no
  preprocessor flags are passed in.

  The defaults are:
  WRDSIZ32       - 32 bit compiler.
}
{$IFDEF CPU64BITS}
{$DEFINE WRDSIZ64}
{$ELSE}
{$DEFINE WRDSIZ32}
{$ENDIF}

program pcode(Input, Output, prd, prr);
{$APPTYPE Console}
{$WEAKLINKRTTI ON}
{$RTTI EXPLICIT METHODS([]) PROPERTIES([]) FIELDS([])}

uses
  System.SysUtils, System.IOUtils, uPCommon;

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

{$IFDEF WRDSIZ32}
{$I 'mpb32.inc'}
{$ENDIF}
{$IFDEF WRDSIZ64}
{$I 'mpb64.inc'}
{$ENDIF}

  { ******************* end of pcom and pint common parameters *********** }

  { internal constants }

  { !!! Need to use the small size memory to self compile, otherwise, by
    definition, pint cannot fit into its own memory. }
  maxstr      = 16777215;  { maximum size of addressing for program/var }
  maxtop      = 16777216;  { maximum size of addressing for program/var+1 }
  maxdef      = 2097152;   { maxstr / 8 for defined bits }

  maxdigh     = 6;       { number of digits in hex representation of maxstr }
  maxdigd     = 8;       { number of digits in decimal representation of maxstr }

  codemax     = maxstr;  { set size of code store to maximum possible }

  maxlabel = 5000;       { total possible labels in intermediate }
  resspc   = 0;          { reserve space in heap (if you want) }

  { locations of header files after program block mark, each header
    file is two values, a file number and a single character buffer }
  filres    = 2;         { space reserved for file }
  inputoff  = 0;         { 'input' file address }
  outputoff = 2;         { 'output' file address }
  prdoff    = 4;         { 'prd' file address }
  prroff    = 6;         { 'prr' file address }

  { assigned logical channels for header files }
  inputfn    = 1;        { 'input' file no. }
  outputfn   = 2;        { 'output' file no. }
  prdfn      = 3;        { 'prd' file no. }
  prrfn      = 4;        { 'prr' file no. }

  stringlgth  = 1000;    { longest string length we can buffer }
  maxsp       = 46;      { number of predefined procedures/functions }
  maxins      = 255;     { maximum instruction code, 0-255 or byte }
  maxfil      = 100;     { maximum number of general (temp) files }
  maxalfa     = 10;      { maximum number of characters in alfa type }

  { version numbers }

  majorver   = 1; { major version number }
  minorver   = 4; { minor version number }
  experiment = False; { is version experimental? }

type
  { These equates define the instruction layout. I have choosen a 32 bit
    layout for the instructions defined by (4 bit) digit:

       byte 0:   Instruction code
       byte 1:   P parameter
       byte 2-5: Q parameter

    This means that there are 256 instructions, 256 procedure levels,
    and 2gb of total addressing. This could be 4gb if we Get rid of the
    need for negatives. }
  lvltyp      = 0..255;     { procedure/function level }
  instyp      = 0..maxins;  { instruction }
  address     = -maxstr..maxtop; { address }

  beta        = packed array [1..25] of Char; { error message }
  settype     = set of setlow..sethigh;
  alfainx     = 1..maxalfa; { index for alfa type }
  alfa        = packed array [alfainx] of Char;
//byte        = 0..255; { 8-bit byte }
  bytfil      = packed file of Byte; { untyped file of bytes }
  fileno      = 0..maxfil; { logical file number }
  { VAR reference block }
  varptr       = ^varblk;
  varblk       = record
    next: varptr; { next entry }
    s, e: address { start and end address of block }
  end;
  { with reference block }
  wthptr       = ^wthblk;
  wthblk       = record
    next: wthptr; { next entry }
    b: address    { address of block }
  end;

var
  pc          : address;   { program address register }
  pctop, lsttop: address;  { top of code store }
  gbtop, gbsiz: address;   { top of globals, size of globals }
  gbset       : Boolean;   { global size was set }
  op : instyp; p : lvltyp; q : Integer;  { instruction register }
  q1, q2: Integer; { extra parameters }
  store       : packed array [0..maxstr] of Byte; { complete program storage }
  storedef    : packed array [0..maxdef] of Byte; { defined bits }
  sdi         : 0..maxdef; { index for that }
  cp          : address;  { pointer to next free constant position }
  mp, sp, np, ep: address;  { address registers  }
  { mp  points to beginning of a data segment
    sp  points to top of the stack
    ep  points to the maximum extent of the stack
    np  points to top of the dynamically allocated area }
  bitmsk      : packed array [0..7] of Byte; { bits in byte }

  interpreting: Boolean;

  prd, prr    : Text; { prd for read only, prr for write only  }

  instr       : array [instyp] of alfa; { mnemonic instruction codes }
  sptable     : array [0..maxsp] of alfa; { standard functions and procedures }
  insp        : array [instyp] of Boolean; { instruction includes a p parameter }
  insq        : array [instyp] of 0..32; { length of q parameter }
  srclin      : Integer; { current source line executing }
  option      : array ['a'..'z'] of Boolean; { option array }

  { check flags: these turn on runtime checks }
  dochkovf    : Boolean;    { check arithmetic overflow }

  { debug flags: turn these on for various dumps and traces }
  dodmpins    : Boolean;    { dump instructions after assembly }
  dodmplab    : Boolean;    { dump label definitions }
  dodmpsto    : Boolean;    { dump storage area specs }
  dotrcrot    : Boolean;    { trace routine executions }
  dotrcins    : Boolean;    { trace instruction executions }
  dopmd       : Boolean;    { perform post-mortem dump on error }
  dosrclin    : Boolean;    { add source line sets to code }
  dotrcsrc    : Boolean;    { trace source line executions (requires dosrclin) }
  dodmpspc    : Boolean;    { dump heap space after execution }
  dorecycl    : Boolean;    { obey heap space recycle requests }
  { invoke a special recycle mode that creates single word entries on
    recycle of any object, breaking off and recycling the rest. Once
    allocated, each entry exists forever, and accesses to it can be
    checked. }
  dochkrpt    : Boolean;    { check reuse of freed entry (automatically
                              invokes dorecycl = False }
  dochkdef    : Boolean;    { check undefined accesses }

  filtable    : array [1..maxfil] of Text; { general (temp) text file holders }
  nfiltable   : array [1..maxfil] of string;
  { general (temp) binary file holders }
  bfiltable   : array [1..maxfil] of bytfil;
  { file state holding }
  filstate    : array [1..maxfil] of (fclosed, fread, fwrite);
  { file buffer full status }
  filbuff     : array [1..maxfil] of Boolean;
  varlst      : varptr; { active var block pushdown stack }
  varfre      : varptr; { free var block entries }
  wthlst      : wthptr; { active with block pushdown stack }
  wthcnt      : Integer; { number of outstanding with levels }
  wthfre      : wthptr; { free with block entries }
  errsinprg   : Integer; { errors in source program }
  maxpow16    : Integer; { maximum power of 16 }
  hexdig      : Integer; { digits in unsigned hex }

  { locally used for interpreting one instruction }
  ad, ad1, ad2   : address;
  b              : Boolean;
  i, j, k, i1, i2: Integer;
  c              : Char;
  i3, i4         : Integer;
  r1, r2         : Real;
  b1, b2         : Boolean;
  s1, s2         : settype;
  c1             : Char;
  a1, a2, a3     : address;
  pcs            : address;
  bai            : Integer;

  SrcFile, DstFile: string;

{ -------------------------------------------------------------------- }

{ Low level error check and handling }

{ print in hex (carefull, it chops high digits freely!) }

procedure wrthex(v: Integer; { value } f: Integer { field });
var
  p, i, d, t, n: Integer;
  digits: packed array [1..inthex] of Char;

  function digit(d: Integer): Char;
  begin
    if d < 10 then
      c := Chr(d + Ord('0'))
    else
      c := Chr(d - 10 + Ord('A'));
    digit := c
  end { digit };

begin
  n := inthex; { number of digits }
  if v < 0 then
  begin { signed }
    v := v + 1 + maxint; { convert number to 31 bit unsigned }
    t := v div maxpow16 + 8; { extract high digit }
    digits[inthex] := digit(t); { place high digit }
    v := Mod2(v, maxpow16); { remove digit }
    n := inthex - 1 { set number of digits-1 }
  end;
  p := 1;
  for i := 1 to n do
  begin
    d := Mod2(v div p, 16); { extract digit }
    digits[i] := digit(d); { place }
    if i < inthex then
      p := p * 16
  end;
  for i := f downto 1 do
    Write(digits[i]) { output }
end { wrthex };

procedure dmpmem(s, e: address);
var
  i, x: Integer;
  bs: array [1..16] of Byte;
  f, l: Boolean;
  ba: address;
begin
  l := False;
  for i := 1 to 16 do
    bs[i] := 0;
  while s <= e do
  begin
    ba := s;
    i := 1;
    f := True;
    while (s <= e) and (i <= 16) do
    begin
      if bs[i] <> store[s] then
        f := False;
      bs[i] := store[s];
      s := s + 1;
      i := i + 1
    end;
    if not f or (i < 16) then
    begin
      if l then
      begin
        Writeln;
        for x := 1 to maxdigh do
          Write('*');
        Write(': ');
        for x := 1 to 16 do
          Write('** ');
      end;
      Writeln;
      wrthex(ba, maxdigh);
      Write(': ');
      for x := 1 to i - 1 do
      begin
        wrthex(bs[x], 2);
        Write(' ')
      end;
      l := False
    end
    else
      l := True
  end
end { dmpmem };

procedure pmd;
begin
  if dopmd then
  begin
    Writeln;
    Write ('pc = '); wrthex(pcs, maxdigh);
    Write(' op = '); wrthex(op, 2);
    Write(' sp = '); wrthex(sp, maxdigh);
    Write(' mp = '); wrthex(mp, maxdigh);
    Write(' np = '); wrthex(np, maxdigh);
    Write(' cp = '); wrthex(cp, maxdigh);
    Writeln;
    Writeln('------------------------------------------------------------' +
            '-------------');
    Writeln; Writeln('Stack');     Writeln; dmpmem(pctop, sp - 1); Writeln;
    Writeln; Writeln('Constants'); Writeln; dmpmem(cp, maxstr);    Writeln;
    Writeln; Writeln('Heap');      Writeln; dmpmem(np, cp - 1);    Writeln;
  end
end; { pmd }

procedure errori(passtr: beta);
begin
  Writeln;
  Write('*** Runtime error');
  if srclin > 0 then
    Write(' [', srclin: 1, ']');
  Writeln(': ', string(passtr));
  pmd;
  Abort
end; { errori }

{ get bit from defined array }

function getdef(a: address): Boolean;
var
  b: Byte;
  r: Boolean;
begin
  if dochkdef then
  begin
    b := storedef[a div 8]; { get byte }
    r := Odd(b div bitmsk[Mod2(a, 8)])
  end
  else
    r := True; { always set defined }
  getdef := r
end { getdef };

{ put bit to defined array }

procedure putdef(a: address; b: Boolean);
var
  sb: Byte;
  r: Boolean;
begin
  if dochkdef then
  begin
    sb := storedef[a div 8]; { get byte }
    { test bit as is }
    r := Odd(sb div bitmsk[Mod2(a, 8)]);
    if r <> b then
    begin
      if b then
        sb := sb + bitmsk[Mod2(a, 8)]
      else
        sb := sb - bitmsk[Mod2(a, 8)];
      storedef[a div 8] := sb
    end
  end
end { putdef };

procedure chkdef(a: address);
begin
  if dochkdef then
    if not getdef(a) then
      errori('Undefined location access')
end { chkdef };

{ -------------------------------------------------------------------- }

{ Accessor functions

  These translate store variables to internal, and convert to and from store RAM
  formats.

  The acessors are fairly machine independent, they rely here on the machine
  being byte addressable. The endian format is inherent to the machine.

  The exception are the Get/put int8,16,32,64 and 128 bit routines, which are
  dependent on the endian mode of the machine.

}

function getint(a: address): Integer;
var
  r: record
       case Boolean of
         True: (i: Integer);
         False: (b: packed array [1..intsize] of Byte);
     end;
  i: 1..intsize;
begin
  if dochkdef then
    chkdef(a);
  for i := 1 to intsize do
    r.b[i] := store[a + i - 1];
  getint := r.i
end { getint };

procedure putint(a: address; x: Integer);
var
  r: record
       case Boolean of
         True: (i: Integer);
         False: (b: packed array [1..intsize] of Byte);
     end;
  i: 1..intsize;
begin
  r.i := x;
  for i := 1 to intsize do
  begin
    store[a + i - 1] := r.b[i];
    putdef(a + i - 1, True)
  end
end { putint };

function getrel(a: address): Real;
var
  r: record
       case Boolean of
         True: (r: Real);
         False: (b: packed array [1..realsize] of Byte);
     end;
  i: 1..realsize;
begin
  if dochkdef then
    chkdef(a);
  for i := 1 to realsize do
    r.b[i] := store[a + i - 1];
  getrel := r.r
end { getrel };

procedure putrel(a: address; f: Real);
var
  r: record
       case Boolean of
         True: (r: Real);
         False: (b: packed array [1..realsize] of Byte);
     end;
  i: 1..realsize;
begin
  r.r := f;
  for i := 1 to realsize do
  begin
    store[a + i - 1] := r.b[i];
    putdef(a + i - 1, True)
  end
end { putrel };

function getbol(a: address): Boolean;
var
  b: Boolean;
begin
  if dochkdef then
    chkdef(a);
  if store[a] = 0 then
    b := False
  else
    b := True;
  getbol := b
end { getbol };

procedure putbol(a: address; b: Boolean);
begin
  store[a] := Ord(b);
  putdef(a, True)
end { putbol };

procedure getset(a: address; var s: settype);
var
  r: record
       case Boolean of
         True: (s: settype);
         False: (b: packed array [1..setsize] of Byte);
  end;
  i: 1..setsize;
begin
  if dochkdef then
    chkdef(a);
  for i := 1 to setsize do
    r.b[i] := store[a + i - 1];
  s := r.s
end { getset };

procedure putset(a: address; s: settype);
var
  r: record
       case Boolean of
         True: (s: settype);
         False: (b: packed array [1..setsize] of Byte);
       end;
  i: 1..setsize;
begin
  r.s := s;
  for i := 1 to setsize do
  begin
    store[a + i - 1] := r.b[i];
    putdef(a + i - 1, True)
  end
end { putset };

function getchr(a: address): Char;
begin
  if dochkdef then
    chkdef(a);
  getchr := Chr(store[a])
end { getchr };

procedure putchr(a: address; c: Char);
begin
  store[a] := Ord(c);
  putdef(a, True)
end { putchr };

function getbyt(a: address): Byte;
begin
  if dochkdef then
    chkdef(a);
  getbyt := store[a]
end { getbyt };

procedure putbyt(a: address; b: Byte);
begin
  store[a] := b;
  putdef(a, True)
end { putbyt };

function getadr(a: address): address;
var
  r: record
       case Boolean of
         True: (a: address);
         False: (b: packed array [1..adrsize] of Byte);
     end;
  i: 1..adrsize;
begin
  if dochkdef then
    chkdef(a);
  for i := 1 to adrsize do
    r.b[i] := store[a + i - 1];
  getadr := r.a
end { getadr };

procedure putadr(a: address; ad: address);
var
  r: record
       case Boolean of
         True: (a: address);
         False: (b: packed array [1..adrsize] of Byte);
     end;
  i: 1..adrsize;
begin
  r.a := ad;
  for i := 1 to adrsize do
  begin
    store[a + i - 1] := r.b[i];
    putdef(a + i - 1, True)
  end
end { putadr };

{ Swap pointer on top with second on stack. The size of the second is given. }

procedure swpstk(l: address);
var
  sb: packed array [1..maxsize] of Byte;
  p: address;
  i: 1..maxsize;
begin
  { get the top pointer }
  p := getadr(sp);
  { load up the second on stack }
  for i := 1 to l do
    sb[i] := store[sp + adrsize + i - 1];
  putadr(sp + l, p); { place pointer at bottom }
  for i := 1 to l do
  begin
    store[sp + i - 1] := sb[i]; { place second as new top }
    putdef(sp + i - 1, True)
  end
end { swpstk };

{ end of accessor functions

{ -------------------------------------------------------------------- }

{ Push/pop

  These routines handle both the data type, and their lengths on the stack.

}

procedure popint(var i: Integer);
begin
  i := getint(sp);
  sp := sp + intsize
end { popint };

procedure pshint(i: Integer);
begin
  sp := sp - intsize;
  putint(sp, i)
end { pshint };

procedure poprel(var r: Real);
begin
  r := getrel(sp);
  sp := sp + realsize
end { poprel };

procedure pshrel(r: Real);
begin
  sp := sp - realsize;
  putrel(sp, r)
end { pshrel };

procedure popset(var s: settype);
begin
  getset(sp, s);
  sp := sp + setsize
end { popset };

procedure pshset(s: settype);
begin
  sp := sp - setsize;
  putset(sp, s)
end { pshset };

procedure popadr(var a: address);
begin
  a := getadr(sp);
  sp := sp + adrsize
end { popadr };

procedure pshadr(a: address);
begin
  sp := sp - adrsize;
  putadr(sp, a)
end { pshadr };

{ list single instruction at address }

procedure lstins(var ad: address);
var
  op: instyp;
  p: lvltyp;
  q, q1, q2: Integer; { instruction register }
begin
  { fetch instruction from byte store }
  op := store[ad];
  ad := ad + 1;
  p := 0;
  q := 0;
  q1 := 0;
  q2 := 0;
  if insp[op] then
  begin
    p := store[ad];
    ad := ad + 1
  end;
  if insq[op] > 0 then
  begin
    if insq[op] = 1 then
      q := store[ad]
    else
    begin
      q := getint(ad);
      if insq[op] > intsize then
        q1 := getint(ad + intsize);
      if insq[op] > intsize * 2 then
        q2 := getint(ad + intsize * 2);
    end;
    ad := ad + insq[op]
  end;
  Write(': ');
  wrthex(op, 2);
  Write(' ', string(instr[op]): 10, '  ');
  if insp[op] then
  begin
    wrthex(p, 2);
    if insq[op] > 0 then
    begin
      Write(',');
      wrthex(q, inthex)
    end;
    if insq[op] > intsize then
    begin
      Write(',');
      wrthex(q1, inthex)
    end;
    if insq[op] > intsize * 2 then
    begin
      Write(',');
      wrthex(q2, inthex)
    end
  end
  else if insq[op] > 0 then
  begin
    Write('   ');
    wrthex(q, inthex);
    if insq[op] > intsize then
    begin
      Write(',');
      wrthex(q1, inthex)
    end;
    if insq[op] > intsize * 2 then
    begin
      Write(',');
      wrthex(q2, inthex)
    end
  end
end { lstins };

{ dump contents of instruction memory }

procedure dmpins;
var
  i: address;
begin
  Writeln;
  Writeln('Contents of instruction memory');
  Writeln;
  Writeln('Addr    Op Ins         P  Q');
  Writeln('----------------------------------');
  i := 0;
  while i < lsttop do
  begin
    wrthex(i, maxdigh);
    lstins(i);
    Writeln
  end;
  Writeln
end { dmpins };

{ align address, upwards }

procedure alignu(algn: address; var flc: address);
var
  l: Integer;
begin
  l := flc - 1;
  flc := l + algn - Mod2(algn + l, algn)
end { alignu };

{ align address, downwards }

procedure alignd(algn: address; var flc: address);
var
  l: Integer;
begin
  l := flc + 1;
  flc := l - algn + Mod2(algn - l, algn)
end { alignd };

{ -------------------------------------------------------------------- }

{ load intermediate file }

procedure load;
type
  labelst = (entered, defined); { label situation }
  labelrg = 0..maxlabel; { label range }
  labelrec = record
    val: address;
    st: labelst
  end;
var
  word: array [alfainx] of Char;
  ch: Char;
  labeltab: array [labelrg] of labelrec;
  labelvalue: address;
  iline: Integer; { line number of intermediate file }

  function ReadNum(var F: Text): Integer;
  var
    IsNegative: Boolean;
  begin
    Result := 0;
    while (CurrentChar(F) = ' ') and not Eoln(F) do
      Read(F, ch);
    IsNegative := CurrentChar(F) = '-';
    if IsNegative then
      Read(F, ch);
    while CharInSet(CurrentChar(F), ['0'..'9']) and not Eoln(F) do
    begin
      Result := Result * 10 + Ord(CurrentChar(F)) - Ord('0');
      Read(F, ch);
    end;
    if IsNegative then
      Result := -Result;
  end { ReadNum };

  procedure init;
  var
    i: Integer;
  begin
    for i := 0 to maxins do
      instr[i] := '          ';
    {

      Notes:

      1. Instructions marked with "*" are for internal use only.
         The "*" mark both shows in the listing, and also prevents
         their use in the intermediate file, since only alpha
         characters are allowed as opcode labels.

      2. "---" entries are unused.

    }
    instr[  0]:='lodi      '; insp[  0] := True;  insq[  0] := intsize;
    instr[  1]:='ldoi      '; insp[  1] := False; insq[  1] := intsize;
    instr[  2]:='stri      '; insp[  2] := True;  insq[  2] := intsize;
    instr[  3]:='sroi      '; insp[  3] := False; insq[  3] := intsize;
    instr[  4]:='lda       '; insp[  4] := True;  insq[  4] := intsize;
    instr[  5]:='lao       '; insp[  5] := False; insq[  5] := intsize;
    instr[  6]:='stoi      '; insp[  6] := False; insq[  6] := 0;
    instr[  7]:='ldcs      '; insp[  7] := False; insq[  7] := intsize;
    instr[  8]:='cvbi      '; insp[  8] := False; insq[  8] := intsize*3;
    instr[  9]:='indi      '; insp[  9] := False; insq[  9] := intsize;
    instr[ 10]:='inci      '; insp[ 10] := False; insq[ 10] := intsize;
    instr[ 11]:='mst       '; insp[ 11] := True;  insq[ 11] := intsize;
    instr[ 12]:='cup       '; insp[ 12] := True;  insq[ 12] := intsize;
    instr[ 13]:='ents      '; insp[ 13] := False; insq[ 13] := intsize;
    instr[ 14]:='retp      '; insp[ 14] := False; insq[ 14] := 0;
    instr[ 15]:='csp       '; insp[ 15] := False; insq[ 15] := 1;
    instr[ 16]:='ixa       '; insp[ 16] := False; insq[ 16] := intsize;
    instr[ 17]:='equa      '; insp[ 17] := False; insq[ 17] := 0;
    instr[ 18]:='neqa      '; insp[ 18] := False; insq[ 18] := 0;
    instr[ 19]:='vbs       '; insp[ 19] := False; insq[ 19] := intsize;
    instr[ 20]:='vbe       '; insp[ 20] := False; insq[ 20] := 0;
    instr[ 21]:='cvbx      '; insp[ 21] := False; insq[ 21] := intsize*3;
    instr[ 22]:='cvbb      '; insp[ 22] := False; insq[ 22] := intsize*3;
    instr[ 23]:='ujp       '; insp[ 23] := False; insq[ 23] := intsize;
    instr[ 24]:='fjp       '; insp[ 24] := False; insq[ 24] := intsize;
    instr[ 25]:='xjp       '; insp[ 25] := False; insq[ 25] := intsize;
    instr[ 26]:='chki      '; insp[ 26] := False; insq[ 26] := intsize;
    instr[ 27]:='cvbc      '; insp[ 27] := False; insq[ 27] := intsize*3;
    instr[ 28]:='adi       '; insp[ 28] := False; insq[ 28] := 0;
    instr[ 29]:='adr       '; insp[ 29] := False; insq[ 29] := 0;
    instr[ 30]:='sbi       '; insp[ 30] := False; insq[ 30] := 0;
    instr[ 31]:='sbr       '; insp[ 31] := False; insq[ 31] := 0;
    instr[ 32]:='sgs       '; insp[ 32] := False; insq[ 32] := 0;
    instr[ 33]:='flt       '; insp[ 33] := False; insq[ 33] := 0;
    instr[ 34]:='flo       '; insp[ 34] := False; insq[ 34] := 0;
    instr[ 35]:='trc       '; insp[ 35] := False; insq[ 35] := 0;
    instr[ 36]:='ngi       '; insp[ 36] := False; insq[ 36] := 0;
    instr[ 37]:='ngr       '; insp[ 37] := False; insq[ 37] := 0;
    instr[ 38]:='sqi       '; insp[ 38] := False; insq[ 38] := 0;
    instr[ 39]:='sqr       '; insp[ 39] := False; insq[ 39] := 0;
    instr[ 40]:='abi       '; insp[ 40] := False; insq[ 40] := 0;
    instr[ 41]:='abr       '; insp[ 41] := False; insq[ 41] := 0;
    instr[ 42]:='not       '; insp[ 42] := False; insq[ 42] := 0;
    instr[ 43]:='and       '; insp[ 43] := False; insq[ 43] := 0;
    instr[ 44]:='ior       '; insp[ 44] := False; insq[ 44] := 0;
    instr[ 45]:='dif       '; insp[ 45] := False; insq[ 45] := 0;
    instr[ 46]:='int       '; insp[ 46] := False; insq[ 46] := 0;
    instr[ 47]:='uni       '; insp[ 47] := False; insq[ 47] := 0;
    instr[ 48]:='inn       '; insp[ 48] := False; insq[ 48] := 0;
    instr[ 49]:='mod       '; insp[ 49] := False; insq[ 49] := 0;
    instr[ 50]:='odd       '; insp[ 50] := False; insq[ 50] := 0;
    instr[ 51]:='mpi       '; insp[ 51] := False; insq[ 51] := 0;
    instr[ 52]:='mpr       '; insp[ 52] := False; insq[ 52] := 0;
    instr[ 53]:='dvi       '; insp[ 53] := False; insq[ 53] := 0;
    instr[ 54]:='dvr       '; insp[ 54] := False; insq[ 54] := 0;
    instr[ 55]:='mov       '; insp[ 55] := False; insq[ 55] := intsize;
    instr[ 56]:='lca       '; insp[ 56] := False; insq[ 56] := intsize;
    instr[ 57]:='deci      '; insp[ 57] := False; insq[ 57] := intsize;
    instr[ 58]:='stp       '; insp[ 58] := False; insq[ 58] := 0;
    instr[ 59]:='ordi      '; insp[ 59] := False; insq[ 59] := 0;
    instr[ 60]:='chr       '; insp[ 60] := False; insq[ 60] := 0;
    instr[ 61]:='ujc       '; insp[ 61] := False; insq[ 61] := intsize;
    instr[ 62]:='rnd       '; insp[ 62] := False; insq[ 62] := 0;
    instr[ 63]:='pck       '; insp[ 63] := False; insq[ 63] := intsize*2;
    instr[ 64]:='upk       '; insp[ 64] := False; insq[ 64] := intsize*2;
    instr[ 65]:='ldoa      '; insp[ 65] := False; insq[ 65] := intsize;
    instr[ 66]:='ldor      '; insp[ 66] := False; insq[ 66] := intsize;
    instr[ 67]:='ldos      '; insp[ 67] := False; insq[ 67] := intsize;
    instr[ 68]:='ldob      '; insp[ 68] := False; insq[ 68] := intsize;
    instr[ 69]:='ldoc      '; insp[ 69] := False; insq[ 69] := intsize;
    instr[ 70]:='stra      '; insp[ 70] := True;  insq[ 70] := intsize;
    instr[ 71]:='strr      '; insp[ 71] := True;  insq[ 71] := intsize;
    instr[ 72]:='strs      '; insp[ 72] := True;  insq[ 72] := intsize;
    instr[ 73]:='strb      '; insp[ 73] := True;  insq[ 73] := intsize;
    instr[ 74]:='strc      '; insp[ 74] := True;  insq[ 74] := intsize;
    instr[ 75]:='sroa      '; insp[ 75] := False; insq[ 75] := intsize;
    instr[ 76]:='sror      '; insp[ 76] := False; insq[ 76] := intsize;
    instr[ 77]:='sros      '; insp[ 77] := False; insq[ 77] := intsize;
    instr[ 78]:='srob      '; insp[ 78] := False; insq[ 78] := intsize;
    instr[ 79]:='sroc      '; insp[ 79] := False; insq[ 79] := intsize;
    instr[ 80]:='stoa      '; insp[ 80] := False; insq[ 80] := 0;
    instr[ 81]:='stor      '; insp[ 81] := False; insq[ 81] := 0;
    instr[ 82]:='stos      '; insp[ 82] := False; insq[ 82] := 0;
    instr[ 83]:='stob      '; insp[ 83] := False; insq[ 83] := 0;
    instr[ 84]:='stoc      '; insp[ 84] := False; insq[ 84] := 0;
    instr[ 85]:='inda      '; insp[ 85] := False; insq[ 85] := intsize;
    instr[ 86]:='indr      '; insp[ 86] := False; insq[ 86] := intsize;
    instr[ 87]:='inds      '; insp[ 87] := False; insq[ 87] := intsize;
    instr[ 88]:='indb      '; insp[ 88] := False; insq[ 88] := intsize;
    instr[ 89]:='indc      '; insp[ 89] := False; insq[ 89] := intsize;
    instr[ 90]:='inca      '; insp[ 90] := False; insq[ 90] := intsize;
    instr[ 91]:='ivtx      '; insp[ 91] := False; insq[ 91] := intsize*3;
    instr[ 92]:='ivtb      '; insp[ 92] := False; insq[ 92] := intsize*3;
    instr[ 93]:='incb      '; insp[ 93] := False; insq[ 93] := intsize;
    instr[ 94]:='incc      '; insp[ 94] := False; insq[ 94] := intsize;
    instr[ 95]:='chka      '; insp[ 95] := False; insq[ 95] := intsize;
    instr[ 96]:='ivtc      '; insp[ 96] := False; insq[ 96] := intsize*3;
    instr[ 97]:='chks      '; insp[ 97] := False; insq[ 97] := intsize;
    instr[ 98]:='chkb      '; insp[ 98] := False; insq[ 98] := intsize;
    instr[ 99]:='chkc      '; insp[ 99] := False; insq[ 99] := intsize;
    instr[100]:='ctp       '; insp[100] := False; insq[100] := intsize;
    instr[101]:='wbs       '; insp[101] := False; insq[101] := intsize;
    instr[102]:='wbe       '; insp[102] := False; insq[102] := intsize;
    instr[103]:='decb      '; insp[103] := False; insq[103] := intsize;
    instr[104]:='decc      '; insp[104] := False; insq[104] := intsize;
    instr[105]:='loda      '; insp[105] := True;  insq[105] := intsize;
    instr[106]:='lodr      '; insp[106] := True;  insq[106] := intsize;
    instr[107]:='lods      '; insp[107] := True;  insq[107] := intsize;
    instr[108]:='lodb      '; insp[108] := True;  insq[108] := intsize;
    instr[109]:='lodc      '; insp[109] := True;  insq[109] := intsize;
    instr[110]:='rgs       '; insp[110] := False; insq[110] := 0;
    instr[111]:='---       '; insp[111] := False; insq[111] := 0;
    instr[112]:='ipj       '; insp[112] := True;  insq[112] := intsize;
    instr[113]:='cip       '; insp[113] := True;  insq[113] := 0;
    instr[114]:='lpa       '; insp[114] := True;  insq[114] := intsize;
    instr[115]:='---       '; insp[115] := False; insq[115] := 0;
    instr[116]:='---       '; insp[116] := False; insq[116] := 0;
    instr[117]:='dmp       '; insp[117] := False; insq[117] := intsize;
    instr[118]:='swp       '; insp[118] := False; insq[118] := intsize;
    instr[119]:='tjp       '; insp[119] := False; insq[119] := intsize;
    instr[120]:='lip       '; insp[120] := True;  insq[120] := intsize;
    instr[121]:='---       '; insp[121] := False; insq[121] := 0;
    instr[122]:='---       '; insp[122] := False; insq[122] := 0;
    instr[123]:='ldci      '; insp[123] := False; insq[123] := intsize;
    instr[124]:='ldcr      '; insp[124] := False; insq[124] := intsize;
    instr[125]:='ldcn      '; insp[125] := False; insq[125] := 0;
    instr[126]:='ldcb      '; insp[126] := False; insq[126] := boolsize;
    instr[127]:='ldcc      '; insp[127] := False; insq[127] := charsize;
    instr[128]:='reti      '; insp[128] := False; insq[128] := 0;
    instr[129]:='retr      '; insp[129] := False; insq[129] := 0;
    instr[130]:='retc      '; insp[130] := False; insq[130] := 0;
    instr[131]:='retb      '; insp[131] := False; insq[131] := 0;
    instr[132]:='reta      '; insp[132] := False; insq[132] := 0;
    instr[133]:='---       '; insp[133] := False; insq[133] := 0;
    instr[134]:='ordb      '; insp[134] := False; insq[134] := 0;
    instr[135]:='---       '; insp[135] := False; insq[135] := 0;
    instr[136]:='ordc      '; insp[136] := False; insq[136] := 0;
    instr[137]:='equi      '; insp[137] := False; insq[137] := 0;
    instr[138]:='equr      '; insp[138] := False; insq[138] := 0;
    instr[139]:='equb      '; insp[139] := False; insq[139] := 0;
    instr[140]:='equs      '; insp[140] := False; insq[140] := 0;
    instr[141]:='equc      '; insp[141] := False; insq[141] := 0;
    instr[142]:='equm      '; insp[142] := False; insq[142] := intsize;
    instr[143]:='neqi      '; insp[143] := False; insq[143] := 0;
    instr[144]:='neqr      '; insp[144] := False; insq[144] := 0;
    instr[145]:='neqb      '; insp[145] := False; insq[145] := 0;
    instr[146]:='neqs      '; insp[146] := False; insq[146] := 0;
    instr[147]:='neqc      '; insp[147] := False; insq[147] := 0;
    instr[148]:='neqm      '; insp[148] := False; insq[148] := intsize;
    instr[149]:='geqi      '; insp[149] := False; insq[149] := 0;
    instr[150]:='geqr      '; insp[150] := False; insq[150] := 0;
    instr[151]:='geqb      '; insp[151] := False; insq[151] := 0;
    instr[152]:='geqs      '; insp[152] := False; insq[152] := 0;
    instr[153]:='geqc      '; insp[153] := False; insq[153] := 0;
    instr[154]:='geqm      '; insp[154] := False; insq[154] := intsize;
    instr[155]:='grti      '; insp[155] := False; insq[155] := 0;
    instr[156]:='grtr      '; insp[156] := False; insq[156] := 0;
    instr[157]:='grtb      '; insp[157] := False; insq[157] := 0;
    instr[158]:='grts      '; insp[158] := False; insq[158] := 0;
    instr[159]:='grtc      '; insp[159] := False; insq[159] := 0;
    instr[160]:='grtm      '; insp[160] := False; insq[160] := intsize;
    instr[161]:='leqi      '; insp[161] := False; insq[161] := 0;
    instr[162]:='leqr      '; insp[162] := False; insq[162] := 0;
    instr[163]:='leqb      '; insp[163] := False; insq[163] := 0;
    instr[164]:='leqs      '; insp[164] := False; insq[164] := 0;
    instr[165]:='leqc      '; insp[165] := False; insq[165] := 0;
    instr[166]:='leqm      '; insp[166] := False; insq[166] := intsize;
    instr[167]:='lesi      '; insp[167] := False; insq[167] := 0;
    instr[168]:='lesr      '; insp[168] := False; insq[168] := 0;
    instr[169]:='lesb      '; insp[169] := False; insq[169] := 0;
    instr[170]:='less      '; insp[170] := False; insq[170] := 0;
    instr[171]:='lesc      '; insp[171] := False; insq[171] := 0;
    instr[172]:='lesm      '; insp[172] := False; insq[172] := intsize;
    instr[173]:='ente      '; insp[173] := False; insq[173] := intsize;
    instr[174]:='mrkl*     '; insp[174] := False; insq[174] := intsize;
    instr[175]:='ckvi      '; insp[175] := False; insq[175] := intsize;
    instr[176]:='---       '; insp[176] := False; insq[176] := intsize;
    instr[177]:='---       '; insp[177] := False; insq[177] := intsize;
    instr[178]:='---       '; insp[178] := False; insq[178] := intsize;
    instr[179]:='ckvb      '; insp[179] := False; insq[179] := intsize;
    instr[180]:='ckvc      '; insp[180] := False; insq[180] := intsize;
    instr[181]:='dupi      '; insp[181] := False; insq[181] := 0;
    instr[182]:='dupa      '; insp[182] := False; insq[182] := 0;
    instr[183]:='dupr      '; insp[183] := False; insq[183] := 0;
    instr[184]:='dups      '; insp[184] := False; insq[184] := 0;
    instr[185]:='dupb      '; insp[185] := False; insq[185] := 0;
    instr[186]:='dupc      '; insp[186] := False; insq[186] := 0;
    instr[187]:='cks       '; insp[187] := False; insq[187] := 0;
    instr[188]:='cke       '; insp[188] := False; insq[188] := 0;
    instr[189]:='inv       '; insp[189] := False; insq[189] := 0;
    instr[190]:='ckla      '; insp[190] := False; insq[190] := intsize;
    instr[191]:='cta       '; insp[191] := False; insq[191] := intsize*3;
    instr[192]:='ivti      '; insp[192] := False; insq[192] := intsize*3;
    instr[193]:='lodx      '; insp[193] := True;  insq[193] := intsize;
    instr[194]:='ldox      '; insp[194] := False; insq[194] := intsize;
    instr[195]:='strx      '; insp[195] := True;  insq[195] := intsize;
    instr[196]:='srox      '; insp[196] := False; insq[196] := intsize;
    instr[197]:='stox      '; insp[197] := False; insq[197] := 0;
    instr[198]:='indx      '; insp[198] := False; insq[198] := intsize;
    instr[199]:='chkx      '; insp[199] := False; insq[199] := intsize;
    instr[200]:='ordx      '; insp[200] := False; insq[200] := 0;
    instr[201]:='incx      '; insp[201] := False; insq[201] := intsize;
    instr[202]:='decx      '; insp[202] := False; insq[202] := intsize;
    instr[203]:='ckvx      '; insp[203] := False; insq[203] := intsize;
    instr[204]:='retx      '; insp[204] := False; insq[204] := 0;

    { sav (mark) and rst (release) were removed }
    sptable[ 0]:='get       ';     sptable[ 1]:='put       ';
    sptable[ 2]:='---       ';     sptable[ 3]:='rln       ';
    sptable[ 4]:='new       ';     sptable[ 5]:='wln       ';
    sptable[ 6]:='wrs       ';     sptable[ 7]:='eln       ';
    sptable[ 8]:='wri       ';     sptable[ 9]:='wrr       ';
    sptable[10]:='wrc       ';     sptable[11]:='rdi       ';
    sptable[12]:='rdr       ';     sptable[13]:='rdc       ';
    sptable[14]:='sin       ';     sptable[15]:='cos       ';
    sptable[16]:='exp       ';     sptable[17]:='log       ';
    sptable[18]:='sqt       ';     sptable[19]:='atn       ';
    sptable[20]:='---       ';     sptable[21]:='pag       ';
    sptable[22]:='rsf       ';     sptable[23]:='rwf       ';
    sptable[24]:='wrb       ';     sptable[25]:='wrf       ';
    sptable[26]:='dsp       ';     sptable[27]:='wbf       ';
    sptable[28]:='wbi       ';     sptable[29]:='wbr       ';
    sptable[30]:='wbc       ';     sptable[31]:='wbb       ';
    sptable[32]:='rbf       ';     sptable[33]:='rsb       ';
    sptable[34]:='rwb       ';     sptable[35]:='gbf       ';
    sptable[36]:='pbf       ';     sptable[37]:='rib       ';
    sptable[38]:='rcb       ';     sptable[39]:='nwl       ';
    sptable[40]:='dsl       ';     sptable[41]:='eof       ';
    sptable[42]:='efb       ';     sptable[43]:='fbv       ';
    sptable[44]:='fvb       ';     sptable[45]:='wbx       ';
    sptable[46]:='rbr       ';

    pc := begincode;
    cp := maxstr; { set constants pointer to top of storage }
    for i := 1 to 10 do
      word[i] := ' ';
    for i := 0 to maxlabel do
      with labeltab[i] do
      begin
        val := -1;
        st := entered
      end;
    { initalize file state }
    for i := 1 to maxfil do
    begin
      filstate[i] := fclosed;
      filbuff[i] := False
    end;
    Reset(prd);
    iline := 1; { set 1st line of intermediate }
    gbset := False { global size not set }
  end; { init }

  procedure errorl(passtr: beta); { error in loading }
  begin
    Writeln;
    Writeln('*** Program load error: [', iline: 1, '] ', string(passtr));
    Abort
  end; { errorl }

  procedure dmplabs; { dump label table }
  var
    i: labelrg;
  begin
    Writeln;
    Writeln('Label table');
    Writeln;
    for i := 1 to maxlabel do
      if labeltab[i].val <> -1 then
      begin
        Write('Label: ', i: 5, ' value: ', labeltab[i].val, ' ');
        if labeltab[i].st = entered then
          Writeln('Entered')
        else
          Writeln('Defined')
      end;
    Writeln
  end { dmplabs };

  procedure update(x: labelrg); { when a label definition lx is found }
  var
    curr, succ, ad: address; { resp. current element and successor element
    of a list of future references }
    endlist: Boolean;
    q: address; { instruction register }
  begin
    if labeltab[x].st = defined then
      errorl('duplicated label         ')
    else
    begin
      if labeltab[x].val <> -1 then { forward reference(s) }
      begin
        curr := labeltab[x].val;
        endlist := False;
        while not endlist do
        begin
          ad := curr;
          q := getadr(ad);
          succ := q; { get target address from that }
          q := labelvalue; { place new target address }
          ad := curr;
          putadr(ad, q);
          if succ = -1 then
            endlist := True
          else
            curr := succ
        end
      end;
      labeltab[x].st := defined;
      labeltab[x].val := labelvalue;
    end
  end; { update }

  procedure getnxt; { get next character }
  begin
    ch := ' ';
    if not Eoln(prd) then
      Read(prd, ch)
  end { getnxt };

  procedure skpspc; { skip spaces }
  begin
    while (ch = ' ') and not Eoln(prd) do
      getnxt
  end { skpspc };

  procedure getlin; { get next line }
  begin
    readln(prd);
    iline := iline + 1 { next intermediate line }
  end { getlin };

  procedure assemble; forward;

  procedure generate; { generate segment of code }
  var
    x: Integer; { label number }
    l: Integer;
    again: Boolean;
    ch1: Char;
    ad: address;
    s: string;
  begin
    again := True;
    while again do
    begin
      if Eof(prd) then
        errorl('unexpected eof on input  ');
      getnxt; { first character of line }
      if not CharInSet(ch, ['!', 'l', 'q', ' ', ':', 'o', 'g', 'v', 'f', 'x'])
        then
        errorl('unexpected line start    ');
      case ch of
        '!':
          getlin; { comment }
        'l':
          begin
            x := ReadNum(prd);
            getnxt;
            if ch = '=' then
              Read(prd, labelvalue)
            else
              labelvalue := pc;
            update(x);
            getlin
          end;
        'q':
          begin
            again := False;
            getlin
          end;
        ' ':
          begin
            getnxt;
            while not Eoln(prd) and (ch = ' ') do
              getnxt;
            if not Eoln(prd) and (ch <> ' ') then
              assemble
            else
              getlin
          end;
        ':':
          begin { source line }
            Read(prd, x); { get source line number }
            if dosrclin then
            begin
              { pass source line register instruction }
              store[pc] := 174;
              putdef(pc, True);
              pc := pc + 1;
              putint(pc, x);
              pc := pc + intsize
            end;
            { skip the rest of the line, which would be the
              contents of the source line if included }
            while not Eoln(prd) do
              Read(prd, c); { get next character }
            getlin { source line }
          end;
        'o':
          begin { option }
            getnxt;
            while not Eoln(prd) and (ch = ' ') do
              getnxt;
            repeat
              if not CharInSet(ch, ['a'..'z']) then
                errorl('No valid option found    ');
              ch1 := ch;
              getnxt;
              option[ch1] := ch = '+';
              getnxt;
              case ch1 of
                'o':
                  dochkovf := option[ch1];
                'e':
                  dodmpins := option[ch1];
                'g':
                  dodmplab := option[ch1];
                'a':
                  dodmpsto := option[ch1];
                'f':
                  dotrcrot := option[ch1];
                'm':
                  dotrcins := option[ch1];
                'j':
                  dopmd := option[ch1];
                'h':
                  dosrclin := option[ch1];
                'k':
                  dotrcsrc := option[ch1];
                'w':
                  dodmpspc := option[ch1];
                'n':
                  dorecycl := option[ch1];
                'p':
                  dochkrpt := option[ch1];
                'q':
                  dochkdef := option[ch1];
                { these options are free }

                { these options are used in pcom.pas }
                'b', 'c', 'd', 'i', 'l', 'r', 't', 'v', 'u', 'x', 'y', 'z':
                  ;
                { reserved options }
                's':
                  ; { ISO 7185 standard }
              end
            until not CharInSet(ch, ['a'..'z']);
            getlin
          end;
        'g':
          begin
            Read(prd, gbsiz);
            gbset := True;
            getlin
          end;
        'v':
          begin { variant logical table }
            getnxt;
            skpspc;
            if ch <> 'l' then
              errorl('Label format error       ');
            getnxt;
            Read(prd, x);
            getnxt;
            Read(prd, l);
            cp := cp - (l * intsize + intsize + intsize);
            ad := cp;
            putint(ad, l);
            ad := ad + intsize;
            while not Eoln(prd) do
            begin
              Read(prd, i);
              putint(ad, i);
              ad := ad + intsize;
            end;
            labelvalue := cp;
            update(x);
            getlin
          end;
        'f':
          begin { faults (errors) }
            Read(prd, i);
            errsinprg := errsinprg + i;
            getlin
          end;
        'x':
          begin { external file }
            Read(prd, i);
            Read(prd, s);
            nfiltable[i] := StringReplace(Trim(s), '''', '', [rfReplaceAll]);
            getlin
          end;
      end;
    end
  end; { generate }

  procedure assemble; { translate symbolic code into machine code and store }
  var
    name: alfa;
    r: Real;
    s: settype;
    i, x, s1, lb, ub, l: Integer;
    c: Char;
    str: packed array [1..stringlgth] of Char; { buffer for string constants }

    procedure lookup(x: labelrg); { search in label table }
    begin
      case labeltab[x].st of
        entered:
          begin
            q := labeltab[x].val;
            labeltab[x].val := pc
          end;
        defined: q := labeltab[x].val
      end { case label.. }
    end; { lookup }

    procedure labelsearch;
    var
      x: labelrg;
    begin
      while (ch <> 'l') and not Eoln(prd) do
        Read(prd, ch);
      Read(prd, x);
      lookup(x)
    end; { labelsearch }

    procedure getname;
    var
      i: alfainx;
    begin
      if Eof(prd) then
        errorl('Unexpected eof on input  ');
      for i := 1 to maxalfa do
        word[i] := ' ';
      i := 1; { set 1st character of word }
      if not CharInSet(ch, ['a'..'z']) then
        errorl('No operation label       ');
      while CharInSet(ch, ['a'..'z']) do
      begin
        if i = maxalfa then
          errorl('Opcode label is too long ');
        word[i] := ch;
        i := i + 1;
        ch := ' ';
        if not Eoln(prd) then
          Read(prd, ch); { next character }
      end;
      Move(word, name, SizeOf(name));
    end; { getname }

    procedure storeop;
    begin
      if pc + 1 > cp then
        errorl('Program code overflow    ');
      store[pc] := op;
      putdef(pc, True);
      pc := pc + 1
    end { storeop };

    procedure storep;
    begin
      if pc + 1 > cp then
        errorl('Program code overflow    ');
      store[pc] := p;
      putdef(pc, True);
      pc := pc + 1
    end { storep };

    procedure storeq;
    begin
      if pc + adrsize > cp then
        errorl('Program code overflow    ');
      putint(pc, q);
      pc := pc + intsize
    end { storeq };

    procedure storeq1;
    begin
      if pc + adrsize > cp then
        errorl('Program code overflow    ');
      putint(pc, q1);
      pc := pc + intsize
    end { storeq1 };

  begin
    p := 0;
    q := 0;
    op := 0;
    getname;
    { note this search removes the top instruction from use }
    while (instr[op] <> name) and (op < maxins) do
      op := op + 1;
    if op = maxins then
      errorl('illegal instruction      ');

    case op of { get parameters p,q  }

      { lod, str, lda, lip }
        0, 193, 105, 106, 107, 108, 109, 195,
        2,  70,  71,  72,  73,  74,   4, 120:
        begin
          Read(prd, p, q);
          storeop;
          storep;
          storeq
        end;

      12,  11 { cup, mst }:
        begin
          Read(prd, p);
          storeop;
          storep;
          labelsearch;
          storeq
        end;

      113 { cip }:
        begin
          Read(prd, p);
          storeop;
          storep
        end;

      { equm, neqm, geqm, grtm, leqm, lesm take a parameter }
      142, 148, 154, 160, 166, 172,

      { lao, ixa, mov, dmp, swp }
        5,  16,  55, 117, 118,

      { ldo, sro, ind, inc, dec, ckv, vbs }
        1, 194, 196, 198,  65,  66,  67,  68,  69,   3,  75,  76,  77,  78,  79,
        9,  85,  86,  87,  88,  89,  10,  90,  93,  94,  57, 103, 104, 175, 176,
      177, 178, 179, 180, 201, 202, 203,  19:
        begin
          Read(prd, q);
          storeop;
          storeq
        end;

      { pck, upk }
       63,  64:
        begin
          Read(prd, q);
          Read(prd, q1);
          storeop;
          storeq;
          storeq1
        end;

      { cta, ivt, cvb }
      191,  91,  92,  96, 192,   8,  21,  22,  27:
        begin
          Read(prd, q);
          Read(prd, q1);
          storeop;
          storeq;
          storeq1;
          labelsearch;
          storeq
        end;

      { ujp, fjp, xjp, tjp }
       23,  24,  25, 119,

      { ents, ente }
       13, 173:
        begin
          storeop;
          labelsearch;
          storeq
        end;

      { ipj, lpa }
      112, 114:
        begin
          Read(prd, p);
          storeop;
          storep;
          labelsearch;
          storeq
        end;

       15 { csp }:
        begin
          skpspc;
          getname;
          while name <> sptable[q] do
          begin
            q := q + 1;
            if q > maxsp then
              errorl('std proc/func not found  ')
          end;
          storeop;
          if pc + 1 > cp then
            errorl('Program code overflow    ');
          store[pc] := q;
          putdef(pc, True);
          pc := pc + 1
        end;

        7, 123, 124, 125, 126, 127 { ldc }:
        begin
          case op of { get q }
            123:
              begin
                Read(prd, i);
                storeop;
                if pc + intsize > cp then
                  errorl('Program code overflow    ');
                putint(pc, i);
                pc := pc + intsize
              end;

            124:
              begin
                Read(prd, r);
                cp := cp - realsize;
                alignd(realal, cp);
                if cp <= 0 then
                  errorl('constant table overflow  ');
                putrel(cp, r);
                q := cp;
                storeop;
                storeq
              end;

            125:
              storeop; { p, q = 0 }

            126:
              begin
                Read(prd, q);
                storeop;
                if pc + 1 > cp then
                  errorl('Program code overflow    ');
                putbol(pc, q <> 0);
                pc := pc + 1
              end;

            127:
              begin
                skpspc;
                if CharInSet(ch, ['0'..'9']) then
                begin
                  i := 0;
                  while CharInSet(ch, ['0'..'9']) do
                  begin
                    i := i * 10 + Ord(ch) - Ord('0');
                    getnxt
                  end;
                  c := Chr(i);
                end
                else
                begin
                  if ch <> '''' then
                    errorl('illegal character        ');
                  getnxt;
                  c := ch;
                  getnxt;
                  if ch <> '''' then
                    errorl('illegal character        ');
                end;
                storeop;
                if pc + 1 > cp then
                  errorl('Program code overflow    ');
                putchr(pc, c);
                pc := pc + 1
              end;
              7:
              begin
                skpspc;
                if ch <> '(' then
                  errorl('ldcs() expected          ');
                s := [];
                getnxt;
                while ch <> ')' do
                begin
                  s1 := ReadNum(prd);
                  getnxt;
                  s := s + [s1]
                end;
                cp := cp - setsize;
                alignd(setal, cp);
                if cp <= 0 then
                  errorl('constant table overflow  ');
                putset(cp, s);
                q := cp;
                storeop;
                storeq
              end
          end
        end;

       26,  95,  97,  98,  99, 190, 199 { chk }:
        begin
          Read(prd, lb, ub);
          if (op = 95) or (op = 190) then
            q := lb
          else
          begin
            cp := cp - intsize;
            alignd(intal, cp);
            if cp <= 0 then
              errorl('constant table overflow  ');
            putint(cp, ub);
            cp := cp - intsize;
            alignd(intal, cp);
            if cp <= 0 then
              errorl('constant table overflow  ');
            putint(cp, lb);
            q := cp
          end;
          storeop;
          storeq
        end;

       56 { lca }:
        begin
          Read(prd, l);
          skpspc;
          for i := 1 to stringlgth do
            str[i] := ' ';
          if ch <> '''' then
            errorl('bad string format        ');
          i := 0;
          repeat
            if Eoln(prd) then
              errorl('unterminated string      ');
            getnxt;
            c := ch;
            if (ch = '''') and (CurrentChar(prd) = '''') then
            begin
              getnxt;
              c := ' '
            end;
            if c <> '''' then
            begin
              if i >= stringlgth then
                errorl('string overflow          ');
              str[i + 1] := ch; { accumulate string }
              i := i + 1
            end
          until c = '''';
          { place in storage }
          cp := cp - l;
          if cp <= 0 then
            errorl('constant table overflow  ');
          q := cp;
          for x := 1 to l do
            putchr(q + x - 1, str[x]);
          { this should have worked, the for loop is faulty
            because the calculation for end is done after the i
            set
          for i := 0 to i-1 do putchr(q+i, str[i+1]);
          }
          storeop;
          storeq
        end;

       14, 128, 129, 130, 131, 132, 204, { ret }

      { equ, neq, geq, grt, leq, les with no parameter }
       17, 137, 138, 139, 140, 141,  18, 143, 144, 145, 146, 147, 149, 150, 151,
      152, 153, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165, 167, 168, 169,
      170, 171,

       59, 133, 134, 135, 136, 200, { ord }

        6,  80,  81,  82,  83,  84, 197, { sto }

      { eof, adi, adr, sbi, sbr, sgs, flt, flo, trc, ngi, ngr, sqi, sqr, abi,
        abr, not, and, ior, dif, int, uni, inn, mod, odd, mpi, mpr, dvi, dvr,
        stp, chr, rnd, rgs, fbv, fvb, ctp }
       28,  29,  30,  31,  32,  33,  34,  35,  36,  37,  38,  39,  40,  41,  42,
       43,  44,  45,  46, 47,   48,  49,  50,  51,  52,  53,  54,  58,  60,  62,
      110, 111, 115, 116, 100, 101, 102,

      { dupi, dupa, dupr, dups, dupb, dupc, cks, cke, inv, vbe }
      181, 182, 183, 184, 185, 186, 187, 188, 189, 20:
        storeop;

      { ujc must have same length as ujp, so we output a dummy q argument }
       61 { ujc }:
        begin
          storeop;
          q := 0;
          storeq
        end
    end;
    getlin { next intermediate line }
  end; { assemble }

  procedure prtrng(a, b: address);
  var
    i: 1..maxdigh;
  begin
    wrthex(a, maxdigh);
    Write('-');
    if b + 1 > a then
      wrthex(b, maxdigh)
    else
      for i := 1 to maxdigh do
        Write('*');
    Writeln(' (', b + 1 - a: maxdigd, ')')
  end { prtrng };

begin
  init;
  generate;
  pctop := pc; { save top of code store }
  gbtop := pctop + gbsiz; { set top of globals }
  lsttop := pctop; { save as top of listing }
  pc := 0;
  generate;
  if not gbset then
    errorl('global space not set     ');
  alignu(stackal, pctop); { align the end of code for globals }
  alignd(heapal, cp); { align the start of cp for stack top }
  gbtop := pctop + gbsiz; { set top of globals }
  alignu(gbsal, gbtop); { align the globals top }
  if dodmpsto then
  begin { dump storage overview }
    Writeln;
    Writeln('Storage areas occupied');
    Writeln;
    Write('Program     ');
    prtrng(0, pctop - 1);
    Write('Globals     ');
    prtrng(pctop, gbtop - 1);
    Write('Stack/Heap  ');
    prtrng(gbtop, cp - 1);
    Write('Constants   ');
    prtrng(cp, maxstr);
    Writeln
  end;
  if dodmpins then
    dmpins; { Debug: dump instructions from store }
  if dodmplab then
    dmplabs { Debug: dump label definitions }
end; { load }

{ ------------------------------------------------------------------------ }

{ runtime handlers }

procedure varenter(s, e: address);
var
  vp: varptr;
begin
  if varfre <> nil then
  begin
    vp := varfre;
    varfre := vp^.next
  end
  else
    new(vp);
  vp^.s := s;
  vp^.e := e;
  vp^.next := varlst;
  varlst := vp
end { varenter };

procedure varexit;
var
  vp: varptr;
begin
  if varlst = nil then
    errori('VAR block list empty     ');
  vp := varlst;
  varlst := vp^.next;
  vp^.next := varfre;
  varfre := vp
end { varexit };

function varlap(s, e: address): Boolean;
var
  vp: varptr;
  f: Boolean;
begin
  vp := varlst;
  f := False;
  while (vp <> nil) and not f do
  begin
    f := (vp^.e >= s) and (vp^.s <= e);
    vp := vp^.next
  end;
  varlap := f
end { varlap };

procedure withenter(b: address);
var
  wp: wthptr;
begin
  if wthfre <> nil then
  begin
    wp := wthfre;
    wthfre := wp^.next
  end
  else
    new(wp);
  wp^.b := b;
  wp^.next := wthlst;
  wthlst := wp;
  wthcnt := wthcnt + 1
end { withenter };

procedure withexit;
var
  wp: wthptr;
begin
  if wthlst = nil then
    errori('With base list empty     ');
  wp := wthlst;
  wthlst := wp^.next;
  wp^.next := wthfre;
  wthfre := wp;
  wthcnt := wthcnt - 1
end { withexit };

function withsch(b: address): Boolean;
var
  wp: wthptr;
  f: Boolean;
begin
  wp := wthlst;
  f := False;
  while (wp <> nil) and not f do
  begin
    f := wp^.b = b;
    wp := wp^.next
  end;
  withsch := f
end { withsch };

function base(ld: Integer): address;
var
  ad: address;
begin
  ad := mp;
  while ld > 0 do
  begin
    ad := getadr(ad + marksl);
    ld := ld - 1
  end;
  base := ad
end; { base }

procedure compare;
{ comparing is only correct if result by comparing integers will be }
begin
  popadr(a2);
  popadr(a1);
  i := 0;
  b := True;
  while b and (i < q) do
  begin
    chkdef(a1 + i);
    chkdef(a2 + i);
    if store[a1 + i] = store[a2 + i] then
      i := i + 1
    else
      b := False
  end;
  if i = q then
    i := i - 1 { point at last location }
end; { compare }

procedure valfil(fa: address); { attach file to file entry }
var
  i, ff: Integer;
begin
  if store[fa] = 0 then
  begin { no file }
    if fa = pctop + inputoff then
      ff := inputfn
    else if fa = pctop + outputoff then
      ff := outputfn
    else if fa = pctop + prdoff then
      ff := prdfn
    else if fa = pctop + prroff then
      ff := prrfn
    else
    begin
      i := 5; { start search after the header files }
      ff := 0;
      while i <= maxfil do
      begin
        if filstate[i] = fclosed then
        begin
          ff := i;
          i := maxfil
        end;
        i := i + 1
      end;
      if ff = 0 then
        errori('To many files            ');
    end;
    store[fa] := ff;
    putdef(fa, True)
  end
end { valfil };

procedure valfilwm(fa: address); { validate file write mode }
begin
  valfil(fa); { validate file address }
  if filstate[store[fa]] <> fwrite then
    errori('File not in write mode   ')
end { valfilwm };

procedure valfilrm(fa: address); { validate file read mode }
begin
  valfil(fa); { validate file address }
  if filstate[store[fa]] <> fread then
    errori('File not in read mode    ')
end { valfilrm };

procedure getop; { get opcode }
begin
  op := store[pc];
  pc := pc + 1
end { getop };

procedure getp; { get p parameter }
begin
  p := store[pc];
  pc := pc + 1
end { getp };

procedure getq; { get q parameter }
begin
  q := getint(pc);
  pc := pc + intsize
end { getq };

procedure getq1; { get q1 parameter }
begin
  q1 := getint(pc);
  pc := pc + intsize
end { getq1 };

procedure getq2; { get q2 parameter }
begin
  q2 := getint(pc);
  pc := pc + intsize
end { getq2 };

{

   Blocks in the heap are dead simple. The block begins with a length, including
   the length itself. If the length is positive, the block is free. If negative,
   the block is allocated. This means that AddressOfBLock+Abs(lengthOfBlock) is
   address of the next block, and RequestedSize <= LengthOfBLock+adrsize is a
   reasonable test for if a free block fits the requested size, since it will
   never be True of occupied blocks.

}

{ report all space in heap }

procedure repspc;
var
  l, ad: address;
begin
  Writeln;
  Writeln('Heap space breakdown');
  Writeln;
  ad := gbtop; { index the bottom of heap }
  while ad < np do
  begin
    l := getadr(ad); { get next block length }
    Write('addr: ');
    wrthex(ad, maxdigh);
    Write(': ', Abs(l): 6, ': ');
    if l >= 0 then
      Writeln('free')
    else
      Writeln('alloc');
    ad := ad + Abs(l)
  end
end { repspc };

{ find free block using length }

procedure fndfre(len: address; var blk: address);
var
  l, b: address;
begin
  b := 0; { set no block found }
  l := 0;
  blk := gbtop; { set to bottom of heap }
  while blk < np do
  begin { search blocks in heap }
    l := getadr(blk); { get length }
    if (Abs(l) < heapal) or (Abs(l) > np) then
      errori('Heap format invalid      ');
    if l >= len + adrsize then
    begin
      b := blk;
      blk := np
    end { found }
    else
      blk := blk + Abs(l) { go next block }
  end;
  if b > 0 then
  begin { block was found }
    putadr(b, -l); { allocate block }
    blk := b + adrsize; { set base address }
    if l > len + adrsize + adrsize + resspc then
    begin
      { If there is enough room for the block, header, and another header,
        then a reserve factor if desired. }
      putadr(b, -(len + adrsize)); { allocate block }
      b := b + len + adrsize; { go to top of allocated block }
      putadr(b, l - (len + adrsize)) { set length of stub space }
    end
  end
  else
    blk := 0 { set no block found }
end { fndfre };

{ coalesce space in heap }

procedure cscspc;
var
  ad, ad1, l, l1: address;
begin
  { first, colapse all free blocks at the heap top }
  ad1 := 0;
  l := 0;
  while (l >= 0) and (np > gbtop) do
  begin
    { find last entry }
    ad := gbtop;
    while ad < np do
    begin
      ad1 := ad;
      ad := ad + Abs(getadr(ad))
    end;
    l := getadr(ad1); { get header length }
    if l >= 0 then
      np := ad1; { release to free space }
  end;
  { now, walk up and collapse adjacent free blocks }
  ad := gbtop; { index bottom }
  while ad < np do
  begin
    l := getadr(ad); { get header length }
    if l >= 0 then
    begin { free }
      ad1 := ad + l; { index next block }
      if ad1 < np then
      begin { not against end }
        l1 := getadr(ad1); { get length next }
        if l1 >= 0 then
          putadr(ad, l + l1) { both blocks are free, combine the blocks }
        else
          ad := ad + l + Abs(l1) { skip both blocks }
      end
      else
        ad := ad1 { skip to end, done }
    end
    else
      ad := ad + Abs(l) { this block is not free, skip it }
  end
end { cscspc };

{ allocate space in heap }

procedure newspc(len: address; var blk: address);
var
  ad, ad1: address;
begin
  alignu(adrsize, len); { align to units of address }
  fndfre(len, blk); { try finding an existing free block }
  if blk = 0 then
  begin { allocate from heap top }
    ad := np; { save base of new block }
    np := np + (len + adrsize); { find new heap top }
    ad1 := np; { save address }
    alignu(heapal, np); { align to arena }
    len := len + (np - ad1); { adjust length upwards for alignment }
    if np > sp then
      errori('Store overflow: dynamic  ');
    putadr(ad, -(len + adrsize)); { allocate block }
    blk := ad + adrsize { index start of block }
  end;
  { clear block and set undefined }
  for ad := blk to blk + len - 1 do
  begin
    store[ad] := 0;
    putdef(ad, False)
  end
end { newspc };

{ dispose of space in heap }

procedure dspspc(len, blk: address);
var
  ad: address;
begin
  if blk = 0 then
    errori('Dispose uninit pointer   ')
  else if blk = nilval then
    errori('Dispose nil pointer      ')
  else if (blk < gbtop) or (blk >= np) then
    errori('Bad pointer value        ');
  ad := blk - adrsize; { index header }
  if getadr(ad) >= 0 then
    errori('Block already freed      ');
  if dorecycl and not dochkrpt then
  begin { obey recycling requests }
    putadr(ad, Abs(getadr(ad))); { set block free }
    cscspc { coalesce free space }
  end
  else if dochkrpt then
  begin { perform special recycle }
    { check can break off top block }
    len := Abs(getadr(ad)); { get length }
    if len >= adrsize * 2 then
      putadr(ad + adrsize, Abs(getadr(ad)) - adrsize);
    { the "marker" is a block with a single address. Since it can't
      hold more than that, it will never be reused }
    putadr(ad, adrsize) { indicate freed but fixed block }
  end
end { dspspc };

{ check pointer indexes free entry }

function isfree(blk: address): Boolean;
begin
  isfree := getadr(blk - adrsize) = adrsize
end { isfree };

{ system routine call}

procedure callsp;
var
  line: Boolean;
  i, j, w, l, f: Integer;
  c: Char;
  b: Boolean;
  ad, ad1: address;
  r: Real;
  fn: fileno;
  mn, mx: Integer;
  FileName: string;

  procedure readi(var f: Text; var i: Integer);
  var
    s: Integer;
    d: Integer;
  begin
    s := +1; { set sign }
    { skip leading spaces }
    while (CurrentChar(f) = ' ') and not Eof(f) do
      Get(f);
    if Eof(f) then
      errori('End of file              ');
    if not CharInSet(CurrentChar(f), ['+', '-', '0'..'9']) then
      errori('Invalid integer format   ');
    if CurrentChar(f) = '+' then
      Get(f)
    else if CurrentChar(f) = '-' then
    begin
      Get(f);
      s := -1
    end;
    if not CharInSet(CurrentChar(f), ['0'..'9']) then
      errori('Invalid integer format   ');
    i := 0; { clear initial value }
    while CharInSet(CurrentChar(f), ['0'..'9']) do
    begin { parse digit }

      d := Ord(CurrentChar(f)) - Ord('0');
      if (i > maxint div 10) or
        ((i = maxint div 10) and (d > Mod2(maxint, 10))) then
        errori('Input value overflows    ');
      i := i * 10 + d; { add in new digit }
      Get(f)

    end;
    i := i * s { place sign }
  end { readi };

  procedure readr(var f: Text; var r: Real);
  var
    i: Integer; { integer holding }
    e: Integer; { exponent }
    d: Integer; { digit }
    s: Boolean; { sign }

    { find power of ten }

    function pwrten(e: Integer): Real;
    var
      t: Real; { accumulator }
      p: Real; { current power }
    begin
      p := 1.0E+1; { set 1st power }
      t := 1.0; { initalize result }
      repeat
        if Odd(e) then
          t := t * p; { if bit set, add this power }
        e := e div 2; { index next bit }
        p := Sqr(p) { find next power }
      until e = 0;
      pwrten := t
    end { pwrten };

  begin
    e := 0; { clear exponent }
    s := False; { set sign }
    r := 0.0; { clear result }
    { skip leading spaces }
    while (CurrentChar(f) = ' ') and not Eof(f) do
      Get(f);
    if Eof(f) then
      errori('End of file              ');
    { get any sign from number }
    if CurrentChar(f) = '-' then
    begin
      Get(f);
      s := True
    end
    else if CurrentChar(f) = '+' then
      Get(f);
    if not CharInSet(CurrentChar(f), ['0'..'9']) then
      errori('Invalid real format      ');
    while CharInSet(CurrentChar(f), ['0'..'9']) do
    begin { parse digit }
      d := Ord(CurrentChar(f)) - Ord('0');
      r := r * 10 + d; { add in new digit }
      Get(f)
    end;
    if CharInSet(CurrentChar(f), ['.', 'e', 'E']) then
    begin { it's a real }
      if CurrentChar(f) = '.' then
      begin { decimal point }
        Get(f); { skip '.' }
        if not CharInSet(CurrentChar(f), ['0'..'9']) then
          errori('Invalid real format      ');
        while CharInSet(CurrentChar(f), ['0'..'9']) do
        begin { parse digit }
          d := Ord(CurrentChar(f)) - Ord('0');
          r := r * 10 + d; { add in new digit }
          Get(f);
          e := e - 1 { count off right of decimal }
        end;
      end;
      if CharInSet(CurrentChar(f), ['e', 'E']) then
      begin { exponent }
        Get(f); { skip 'e' }
        if not CharInSet(CurrentChar(f), ['0'..'9', '+', '-']) then
          errori('Invalid real format      ');
        readi(f, i); { get exponent }
        { find with exponent }
        e := e + i
      end;
      if e < 0 then
        r := r / pwrten(e)
      else
        r := r * pwrten(e)
    end;
    if s then
      r := -r
  end { readr };

  procedure readc(var f: Text; var c: Char);
  begin
    if Eof(f) then
      errori('End of file              ');
    Read(f, c);
    {$IFDEF MSWINDOWS}
    if c = #$0D then
      Read(f, c);
    {$ENDIF}
    if c = #$0A then
      c := ' ';
  end; { readc }

  procedure writestr(var f: Text; ad: address; w: Integer; l: Integer);
  var
    i: Integer;
  begin { l and w are numbers of characters }
    if w > l then
      for i := 1 to w - l do
        Write(f, ' ')
    else
      l := w;
    for i := 0 to l - 1 do
      Write(f, getchr(ad + i))
  end; { writestr }

  procedure getfile(var f: Text);
  begin
    if Eof(f) then
      errori('End of file              ');
    Get(f);
  end; { getfile }

  procedure putfile(var f: Text; var ad: address; fn: fileno);
  begin
    if not filbuff[fn] then
      errori('File buffer undefined    ');
    Write(f, getchr(ad + fileidsize));
    filbuff[fn] := False
  end; { putfile }

begin
  if q > maxsp then
    errori('Invalid std proc/func    ');

  { trace routine executions }
  if dotrcrot then
    Writeln(pc: 6, '/', sp: 6, '-> ', q: 2);
  case q of
    0 { get }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if varlap(ad + fileidsize, ad + fileidsize) then
          errori('VAR ref file buf modified');
        if fn <= prrfn then
          case fn of
            inputfn:
              getfile(Input);
            outputfn:
              errori('Get on output file       ');
            prdfn:
              getfile(prd);
            prrfn:
              errori('Get on prr file          ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          getfile(filtable[fn])
        end
      end;
    1 { put }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Put on read file         ');
            outputfn:
              putfile(Output, ad, fn);
            prdfn:
              errori('Put on prd file          ');
            prrfn:
              putfile(prr, ad, fn)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          putfile(filtable[fn], ad, fn)
        end
      end;
    { unused placeholder for "release" }
    2 { rst }:
      errori('Invalid std proc/func    ');
    3 { rln }:
      begin
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                if Eof(Input) then
                  errori('End of file              ');
                readln(Input)
              end;
            outputfn:
              errori('Readln on output file    ');
            prdfn:
              begin
                if Eof(prd) then
                  errori('End of file              ');
                readln(prd)
              end;
            prrfn: errori('Readln on prr file       ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          if Eof(filtable[fn]) then
            errori('End of file              ');
          readln(filtable[fn])
        end
      end;
    4 { new }:
      begin
        popadr(ad1);
        newspc(ad1, ad);
        { top of stack gives the length in units of storage  }
        popadr(ad1);
        putadr(ad1, ad)
      end;
    39 { nwl }:
      begin
        popadr(ad1);
        popint(i); { size of record, size of f const list }
        newspc(ad1 + (i + 1) * intsize, ad);
          { alloc record, size of list, number in list }
        ad1 := ad + i * intsize;
        putint(ad1, i + adrsize + 1);
        k := i; { save n tags for later }
        while k > 0 do
        begin
          ad1 := ad1 - intsize;
          popint(j);
          putint(ad1, j);
          k := k - 1
        end;
        { get pointer to dest var, place base above taglist and
          list of fixed consts }
        popadr(ad1);
        putadr(ad1, ad + (i + 1) * intsize)
      end;
    5 { wln }:
      begin
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Writeln on input file    ');
            outputfn:
              Writeln(Output);
            prdfn:
              errori('Writeln on prd file      ');
            prrfn:
              Writeln(prr)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          Writeln(filtable[fn])
        end
      end;
    6 { wrs }:
      begin
        popint(l);
        popint(w);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              writestr(Output, ad1, w, l);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              writestr(prr, ad1, w, l)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          writestr(filtable[fn], ad1, w, l)
        end;
      end;
    41 { eof }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              pshint(Ord(Eof(Input)));
            prdfn:
              pshint(Ord(Eof(prd)));
            outputfn,
            prrfn:
              errori('Eof test on output file  ')
          end
        else
        begin
          if filstate[fn] = fwrite then
            pshint(Ord(True))
          else if filstate[fn] = fread then
            pshint(Ord(Eof(filtable[fn]) and not filbuff[fn]))
          else
            errori('File is not open         ')
        end
      end;
    42 { efb }:
      begin
        popadr(ad);
        valfilrm(ad);
        fn := store[ad];
        { eof is file eof, and buffer not full }
        pshint(Ord(Eof(bfiltable[fn]) and not filbuff[fn]))
      end;
    7 { eln }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        line := False;
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                if Eof(Input) then
                  errori('Eof on file              ');
                line := Eoln(Input)
              end;
            outputfn:
              errori('Eoln output file         ');
            prdfn:
              line := Eoln(prd);
            prrfn:
              errori('Eoln on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          if Eof(filtable[fn]) then
            errori('Eof on file              ');
          line := Eoln(filtable[fn])
        end;
        pshint(Ord(line))
      end;
    8 { wri }:
      begin
        popint(w);
        popint(i);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              Write(Output, i: w);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              Write(prr, i: w)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          Write(filtable[fn], i: w)
        end
      end;
    9 { wrr }:
      begin
        popint(w);
        poprel(r);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              WriteReal(Output, r, w);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              WriteReal(prr, r, w)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          WriteReal(filtable[fn], r, w)
        end;
      end;
    10 { wrc }:
      begin
        popint(w);
        popint(i);
        c := Chr(i);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              Write(Output, c: w);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              Write(prr, c: w)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          Write(filtable[fn], c: w)
        end
      end;
    11 { rdi }:
      begin
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                readi(Input, i);
                putint(ad1, i);
              end;
            outputfn:
              errori('Read on output file      ');
            prdfn:
              begin
                readi(prd, i);
                putint(ad1, i)
              end;
            prrfn:
              errori('Read on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          readi(filtable[fn], i);
          putint(ad1, i)
        end
      end;
    37 { rib }:
      begin
        popint(mx);
        popint(mn);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                readi(Input, i);
                if (i < mn) or (i > mx) then
                  errori('Value read out of range  ');
                putint(ad1, i);
              end;
            outputfn:
              errori('Read on output file      ');
            prdfn:
              begin
                readi(prd, i);
                if (i < mn) or (i > mx) then
                  errori('Value read out of range  ');
                putint(ad1, i)
              end;
            prrfn: errori('Read on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          readi(filtable[fn], i);
          if (i < mn) or (i > mx) then
            errori('Value read out of range  ');
          putint(ad1, i)
        end
      end;
    12 { rdr }:
      begin
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                readr(Input, r);
                putrel(ad1, r);
              end;
            outputfn:
              errori('Read on output file      ');
            prdfn:
              begin
                readr(prd, r);
                putrel(ad1, r)
              end;
            prrfn: errori('Read on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          readr(filtable[fn], r);
          putrel(ad1, r)
        end
      end;
    13 { rdc }:
      begin
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                readc(Input, c);
                putchr(ad1, c);
              end;
            outputfn:
              errori('Read on output file      ');
            prdfn:
              begin
                readc(prd, c);
                putchr(ad1, c);
              end;
            prrfn: errori('Read on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          readc(filtable[fn], c);
          putchr(ad1, c)
        end
      end;
    38 { rcb }:
      begin
        popint(mx);
        popint(mn);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              begin
                readc(Input, c);
                if (Ord(c) < mn) or (Ord(c) > mx) then
                  errori('Value read out of range  ');
                putchr(ad1, c)
              end;
            outputfn:
              errori('Read on output file      ');
            prdfn:
              begin
                readc(prd, c);
                if (Ord(c) < mn) or (Ord(c) > mx) then
                  errori('Value read out of range  ');
                putchr(ad1, c)
              end;
            prrfn: errori('Read on prr file         ')
          end
        else
        begin
          if filstate[fn] <> fread then
            errori('File not in read mode    ');
          readc(filtable[fn], c);
          if (Ord(c) < mn) or (Ord(c) > mx) then
            errori('Value read out of range  ');
          putchr(ad1, c)
        end
      end;
    14 { sin }:
      begin
        poprel(r1);
        pshrel(sin(r1))
      end;
    15 { cos }:
      begin
        poprel(r1);
        pshrel(cos(r1))
      end;
    16 { exp }:
      begin
        poprel(r1);
        pshrel(exp(r1))
      end;
    17 { log }:
      begin
        poprel(r1);
        if r1 <= 0 then
          errori('Cannot find ln <= 0      ');
        pshrel(ln(r1))
      end;
    18 { sqt }:
      begin
        poprel(r1);
        if r1 < 0 then
          errori('Cannot find sqrt < 0     ');
        pshrel(sqrt(r1))
      end;
    19 { atn }:
      begin
        poprel(r1);
        pshrel(arctan(r1))
      end;
    { placeholder for "mark" }
    20 { sav }: errori('Invalid std proc/func    ');
    21 { pag }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Page on read file        ');
            outputfn:
              page(Output);
            prdfn:
              errori('Page on prd file         ');
            prrfn:
              page(prr)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          page(filtable[fn])
        end
      end;
    22 { rsf }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Reset on input file      ');
            outputfn:
              errori('Reset on output file     ');
            prdfn:
              Reset(prd);
            prrfn:
              errori('Reset on prr file        ')
          end
        else
        begin
          if filstate[fn] <> fclosed then
          begin
            if filstate[fn] = fwrite then
            begin
              AddEoln(filtable[fn]);
              Flush(filtable[fn]);
            end;
            CloseFile(filtable[fn]);
          end;
          filstate[fn] := fread;
          if nfiltable[fn] = '' then
            FileName := TPath.Combine(TPath.GetTempPath, Format(p5temp + '%.3d.TXT', [fn - 4]))
          else
            FileName := nfiltable[fn];
          AssignFile(filtable[fn], FileName);
          Reset(filtable[fn]);
          filbuff[fn] := False
        end
      end;
    23 { rwf }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Rewrite on input file    ');
            outputfn:
              errori('Rewrite on output file   ');
            prdfn:
              errori('Rewrite on prd file      ');
            prrfn:
              Rewrite(prr)
          end
        else
        begin
          if filstate[fn] <> fclosed then
          begin
            if filstate[fn] = fwrite then
            begin
              AddEoln(filtable[fn]);
              Flush(filtable[fn]);
            end;
            CloseFile(filtable[fn]);
          end;
          filstate[fn] := fwrite;
          if nfiltable[fn] = '' then
            FileName := TPath.Combine(TPath.GetTempPath, Format(p5temp + '%.3d.TXT', [fn - 4]))
          else
            FileName := nfiltable[fn];
          AssignFile(filtable[fn], FileName);
          Rewrite(filtable[fn])
        end
      end;
    24 { wrb }:
      begin
        popint(w);
        popint(i);
        b := i <> 0;
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              WriteBool(Output, b, w);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              WriteBool(prr, b, w)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          WriteBool(filtable[fn], b, w)
        end
      end;
    25 { wrf }:
      begin
        popint(f);
        popint(w);
        poprel(r);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if w < 1 then
          errori('Width cannot be < 1      ');
        if f < 1 then
          errori('Fraction cannot be < 1   ');
        if fn <= prrfn then
          case fn of
            inputfn:
              errori('Write on input file      ');
            outputfn:
              Write(Output, r: w: f);
            prdfn:
              errori('Write on prd file        ');
            prrfn:
              Write(prr, r: w: f)
          end
        else
        begin
          if filstate[fn] <> fwrite then
            errori('File not in write mode   ');
          Write(filtable[fn], r: w: f)
        end
      end;
    26 { dsp }:
      begin
        popadr(ad1);
        popadr(ad);
        if varlap(ad, ad + ad1 - 1) then
          errori('Dispose of VAR ref block ');
        if withsch(ad) then
          errori('Dispose of with ref block');
        dspspc(ad1, ad)
      end;
    40 { dsl }:
      begin
        popadr(ad1);
        popint(i); { get size of record and n tags }
        ad := getadr(sp + i * intsize); { get rec addr }
        { under us is either the number of tags or the length of the block, if it
          was freed. Either way, it is >= adrsize if not free }
        if getint(ad - intsize) <= adrsize then
          errori('Block already freed      ');
        if i <> getint(ad - intsize) - adrsize - 1 then
          errori('New/dispose tags mismatch');
        ad := ad - intsize * 2;
        ad2 := sp;
        { ad = top of tags in dynamic, ad2 = top of tags in
          stack }
        k := i;
        while k > 0 do
        begin
          if getint(ad) <> getint(ad2) then
            errori('New/dispose tags mismatch');
          ad := ad - intsize;
          ad2 := ad2 + intsize;
          k := k - 1
        end;
        ad := ad + intsize;
        ad1 := ad1 + (i + 1) * intsize;
        if varlap(ad, ad + ad1 - 1) then
          errori('Dispose of VAR ref block ');
        if withsch(ad) then
          errori('Dispose of with ref block');
        dspspc(ad1, ad);
        while i > 0 do
        begin
          popint(j);
          i := i - 1
        end;
        popadr(ad)
      end;
    27 { wbf }:
      begin
        popint(l);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfilwm(ad);
        fn := store[ad];
        for i := 1 to l do
        begin
          chkdef(ad1);
          Write(bfiltable[fn], store[ad1]);
          ad1 := ad1 + 1
        end
      end;
    28 { wbi }:
      begin
        popint(i);
        popadr(ad);
        pshadr(ad);
        pshint(i);
        valfilwm(ad);
        fn := store[ad];
        for i := 1 to intsize do
          Write(bfiltable[fn], store[sp + i - 1]);
        popint(i)
      end;
    45 { wbx }:
      begin
        popint(i);
        popadr(ad);
        pshadr(ad);
        pshint(i);
        valfilwm(ad);
        fn := store[ad];
        Write(bfiltable[fn], store[sp]);
        popint(i)
      end;
    29 { wbr }:
      begin
        poprel(r);
        popadr(ad);
        pshadr(ad);
        pshrel(r);
        valfilwm(ad);
        fn := store[ad];
        for i := 1 to realsize do
          Write(bfiltable[fn], store[sp + i - 1]);
        poprel(r)
      end;
    30 { wbc }:
      begin
        popint(i);
        c := Chr(i);
        popadr(ad);
        pshadr(ad);
        pshint(i);
        valfilwm(ad);
        fn := store[ad];
        for i := 1 to charsize do
          Write(bfiltable[fn], store[sp + i - 1]);
        popint(i)
      end;
    31 { wbb }:
      begin
        popint(i);
        popadr(ad);
        pshadr(ad);
        pshint(i);
        valfilwm(ad);
        fn := store[ad];
        for i := 1 to boolsize do
          Write(bfiltable[fn], store[sp + i - 1]);
        popint(i)
      end;
    32 { rbf }:
      begin
        popint(l);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfilrm(ad);
        fn := store[ad];
        if filbuff[fn] then { buffer data exists }
          for i := 1 to l do
          begin
            store[ad1 + i - 1] := store[ad + fileidsize + i - 1];
            putdef(ad1 + i - 1, True)
          end
        else
        begin
          if Eof(bfiltable[fn]) then
            errori('End of file              ');
          for i := 1 to l do
          begin
            Read(bfiltable[fn], store[ad1]);
            putdef(ad1, True);
            ad1 := ad1 + 1
          end
        end
      end;
    33 { rsb }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        if filstate[fn] = fclosed then
          errori('Cannot reset closed file ');
        filstate[fn] := fread;
        if nfiltable[fn] = '' then
          FileName := TPath.Combine(TPath.GetTempPath, Format(p5temp + '%.3d.BIN', [fn - 4]))
        else
          FileName := nfiltable[fn];
        AssignFile(bfiltable[fn], FileName);
        Reset(bfiltable[fn]);
        filbuff[fn] := False
      end;
    34 { rwb }:
      begin
        popadr(ad);
        valfil(ad);
        fn := store[ad];
        filstate[fn] := fwrite;
        if nfiltable[fn] = '' then
          FileName := TPath.Combine(TPath.GetTempPath, Format(p5temp + '%.3d.BIN', [fn - 4]))
        else
          FileName := nfiltable[fn];
        AssignFile(bfiltable[fn], FileName);
        Rewrite(bfiltable[fn]);
        filbuff[fn] := False
      end;
    35 { gbf }:
      begin
        popint(i);
        popadr(ad);
        valfilrm(ad);
        fn := store[ad];
        if varlap(ad + fileidsize, ad + fileidsize + i - 1) then
          errori('VAR ref file buf modified');
        if filbuff[fn] then
          filbuff[fn] := False
        else
          for j := 1 to i do
            Read(bfiltable[fn], store[ad + fileidsize + j - 1])
      end;
    36 { pbf }:
      begin
        popint(i);
        popadr(ad);
        valfilwm(ad);
        fn := store[ad];
        if not filbuff[fn] then
          errori('File buffer undefined    ');
        for j := 1 to i do
          Write(bfiltable[fn], store[ad + fileidsize + j - 1]);
        filbuff[fn] := False;
      end;
    43 { fbv }:
      begin
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        if fn = inputfn then
          putchr(ad + fileidsize, CurrentChar(Input))
        else if fn = prdfn then
          putchr(ad + fileidsize, CurrentChar(prd))
        else
        begin
          if filstate[fn] = fread then
            putchr(ad + fileidsize, CurrentChar(filtable[fn]))
        end
      end;
    44 { fvb }:
      begin
        popint(i);
        popadr(ad);
        pshadr(ad);
        valfil(ad);
        fn := store[ad];
        { load buffer only if in Read mode, and buffer is
          empty }
        if (filstate[fn] = fread) and not filbuff[fn] then
        begin
          for j := 1 to i do
          begin
            Read(bfiltable[fn], store[ad + fileidsize + j - 1]);
            putdef(ad + fileidsize + j - 1, True)
          end
        end;
        filbuff[fn] := True
      end;
    46 { rbr }:
      begin
        popint(mx);
        popint(mn);
        popint(l);
        popadr(ad1);
        popadr(ad);
        pshadr(ad);
        valfilrm(ad);
        fn := store[ad];
        if filbuff[fn] then { buffer data exists }
          for i := 1 to l do
          begin
            store[ad1 + i - 1] := store[ad + fileidsize + i - 1];
            putdef(ad1 + i - 1, True)
          end
        else
        begin
          if Eof(bfiltable[fn]) then
            errori('End of file              ');
          ad := ad1;
          for i := 1 to l do
          begin
            Read(bfiltable[fn], store[ad1]);
            putdef(ad1, True);
            ad1 := ad1 + 1
          end;
          ad1 := ad
        end;
        { only two cases, char and byte, or integer }
        if l = 1 then
          i := getbyt(ad1)
        else
          i := getint(ad1);
        if (i < mn) or (i > mx) then
          errori('Value read out of range  ')
      end;
  end;
end; { callsp }

procedure dmpdsp(mp: address);
begin
  Writeln;
  Write('Mark @');
  wrthex(mp, 8);
  Writeln;
  Write('sl: '); wrthex(mp + marksl, 8); Write(': '); if getdef(mp + marksl) then wrthex(getadr(mp + marksl), 8) else Write('********'); Writeln;
  Write('dl: '); wrthex(mp + markdl, 8); Write(': '); if getdef(mp + markdl) then wrthex(getadr(mp + markdl), 8) else Write('********'); Writeln;
  Write('ep: '); wrthex(mp + markep, 8); Write(': '); if getdef(mp + markep) then wrthex(getadr(mp + markep), 8) else Write('********'); Writeln;
  Write('sb: '); wrthex(mp + marksb, 8); Write(': '); if getdef(mp + marksb) then wrthex(getadr(mp + marksb), 8) else Write('********'); Writeln;
  Write('et: '); wrthex(mp + market, 8); Write(': '); if getdef(mp + market) then wrthex(getadr(mp + market), 8) else Write('********'); Writeln;
  Write('ra: '); wrthex(mp + markra, 8); Write(': '); if getdef(mp + markra) then wrthex(getadr(mp + markra), 8) else Write('********'); Writeln
end { dmpdsp };

procedure fndpow(var m: Integer; p: Integer; var d: Integer);
begin
  m := 1;
  d := 1;
  while m < maxint div p do
  begin
    m := m * p;
    d := d + 1
  end
end { fndpow };

begin
  if ParamCount > 0 then
    SrcFile := ParamStr(ParamCount)
  else
    SrcFile := 'prd';
  DstFile := 'prr';

  Write('P5 Pascal interpreter vs. ', majorver: 1, '.', minorver: 1);
  if experiment then
    Write('.x');
  Write(' (Built with Delphi)');
  Writeln;
  Writeln;

  if (not TFile.Exists(SrcFile)) or
    FindCmdLineSwitch('?', ['-', '/'], True) or
    FindCmdLineSwitch('-help', ['-'], True) then
  begin
    Write(TPath.GetFileNameWithoutExtension(ParamStr(0)));
    Writeln(' [filename]');
    Exit;
  end;

  AssignFile(prd, SrcFile);
  AssignFile(prr, DstFile);
  try
    Rewrite(prr);

    { construct bit equivalence table }
    i := 1;
    for bai := 0 to 7 do
    begin
      bitmsk[bai] := i;
      i := i * 2
    end;

    for sdi := 0 to maxdef do
      storedef[sdi] := 0; { clear storage defined flags }

    { debug/check flags }
    dochkovf := True; { check arithmetic overflow }
    dodmpins := False; { dump instructions after assembly }
    dodmplab := False; { dump label definitions }
    dodmpsto := False; { dump storage area specs }
    dotrcrot := False; { trace routine executions }
    dotrcins := False; { trace instruction executions }
    dopmd := False; { perform post-mortem dump on error }
    dosrclin := True; { add source line sets to code }
    dotrcsrc := False; { trace source line executions }
    dodmpspc := False; { dump heap space after execution }
    dorecycl := True; { obey heap space recycle requests }
    dochkrpt := False; { check reuse of freed entry }
    dochkdef := True; { check undefined accesses }

    errsinprg := 0; { set no source errors }
    varlst := nil; { set no VAR block entries }
    varfre := nil;
    wthlst := nil; { set no with block entries }
    wthcnt := 0;
    wthfre := nil;
    fndpow(maxpow16, 16, hexdig);

    Writeln('Assembling/loading program');
    load; { assembles and stores code }

    { check and abort if source errors: this indicates a bad intermediate }
    if errsinprg > 0 then
    begin
      Writeln;
      Writeln('*** Source program contains errors: ', errsinprg: 1);
      Abort
    end;

    pc := 0;
    sp := cp;
    np := gbtop;
    mp := cp;
    ep := 5;
    srclin := 0;

    { clear globals }
    for ad := pctop to gbtop - 1 do
    begin
      store[ad] := 0;
      putdef(ad, False)
    end;

    interpreting := True;

    Writeln('Running program');
    Writeln;
    while interpreting do
    begin
      if pc >= pctop then
        errori('pc out of range          ');
      { fetch instruction from byte store }
      pcs := pc; { save starting pc }
      getop;

      { execute }

      { trace executed instructions }
      if dotrcins then
      begin
        wrthex(pcs, maxdigh);
        Write('/');
        wrthex(sp, maxdigh);
        lstins(pcs);
        Writeln
      end;
      case op of
          0 { lodi }:
          begin
            getp;
            getq;
            pshint(getint(base(p) + q))
          end;
        193 { lodx }:
          begin
            getp;
            getq;
            pshint(getbyt(base(p) + q))
          end;
        105 { loda }:
          begin
            getp;
            getq;
            pshadr(getadr(base(p) + q))
          end;
        106 { lodr }:
          begin
            getp;
            getq;
            pshrel(getrel(base(p) + q))
          end;
        107 { lods }:
          begin
            getp;
            getq;
            getset(base(p) + q, s1);
            pshset(s1)
          end;
        108 { lodb }:
          begin
            getp;
            getq;
            pshint(Ord(getbol(base(p) + q)))
          end;
        109 { lodc }:
          begin
            getp;
            getq;
            pshint(Ord(getchr(base(p) + q)))
          end;

          1 { ldoi }:
          begin
            getq;
            pshint(getint(pctop + q))
          end;
        194 { ldox }:
          begin
            getq;
            pshint(getbyt(pctop + q))
          end;
         65 { ldoa }:
          begin
            getq;
            pshadr(getadr(pctop + q))
          end;
         66 { ldor }:
          begin
            getq;
            pshrel(getrel(pctop + q))
          end;
         67 { ldos }:
          begin
            getq;
            getset(pctop + q, s1);
            pshset(s1)
          end;
         68 { ldob }:
          begin
            getq;
            pshint(Ord(getbol(pctop + q)))
          end;
         69 { ldoc }:
          begin
            getq;
            pshint(Ord(getchr(pctop + q)))
          end;

          2 { stri }:
          begin
            getp;
            getq;
            popint(i);
            putint(base(p) + q, i)
          end;
        195 { strx }:
          begin
            getp;
            getq;
            popint(i);
            putbyt(base(p) + q, i)
          end;
         70 { stra }:
          begin
            getp;
            getq;
            popadr(ad);
            putadr(base(p) + q, ad)
          end;
         71 { strr }:
          begin
            getp;
            getq;
            poprel(r1);
            putrel(base(p) + q, r1)
          end;
         72 { strs }:
          begin
            getp;
            getq;
            popset(s1);
            putset(base(p) + q, s1)
          end;
         73 { strb }:
          begin
            getp;
            getq;
            popint(i1);
            b1 := i1 <> 0;
            putbol(base(p) + q, b1)
          end;
         74 { strc }:
          begin
            getp;
            getq;
            popint(i1);
            c1 := Chr(i1);
            putchr(base(p) + q, c1)
          end;

          3 { sroi }:
          begin
            getq;
            popint(i);
            putint(pctop + q, i)
          end;
        196 { srox }:
          begin
            getq;
            popint(i);
            putbyt(pctop + q, i)
          end;
         75 { sroa }:
          begin
            getq;
            popadr(ad);
            putadr(pctop + q, ad)
          end;
         76 { sror }:
          begin
            getq;
            poprel(r1);
            putrel(pctop + q, r1)
          end;
         77 { sros }:
          begin
            getq;
            popset(s1);
            putset(pctop + q, s1)
          end;
         78 { srob }:
          begin
            getq;
            popint(i1);
            b1 := i1 <> 0;
            putbol(pctop + q, b1)
          end;
         79 { sroc }:
          begin
            getq;
            popint(i1);
            c1 := Chr(i1);
            putchr(pctop + q, c1)
          end;

          4 { lda }:
          begin
            getp;
            getq;
            pshadr(base(p) + q)
          end;
          5 { lao }:
          begin
            getq;
            pshadr(pctop + q)
          end;

          6 { stoi }:
          begin
            popint(i);
            popadr(ad);
            putint(ad, i)
          end;
        197 { stox }:
          begin
            popint(i);
            popadr(ad);
            putbyt(ad, i)
          end;
         80 { stoa }:
          begin
            popadr(ad1);
            popadr(ad);
            putadr(ad, ad1)
          end;
         81 { stor }:
          begin
            poprel(r1);
            popadr(ad);
            putrel(ad, r1)
          end;
         82 { stos }:
          begin
            popset(s1);
            popadr(ad);
            putset(ad, s1)
          end;
         83 { stob }:
          begin
            popint(i1);
            b1 := i1 <> 0;
            popadr(ad);
            putbol(ad, b1)
          end;
         84 { stoc }:
          begin
            popint(i1);
            c1 := Chr(i1);
            popadr(ad);
            putchr(ad, c1)
          end;

        127 { ldcc }:
          begin
            pshint(Ord(getchr(pc)));
            pc := pc + 1
          end;
        126 { ldcb }:
          begin
            pshint(Ord(getbol(pc)));
            pc := pc + 1
          end;
        123 { ldci }:
          begin
            i := getint(pc);
            pc := pc + intsize;
            pshint(i)
          end;
        125 { ldcn }: pshadr(nilval) { load nil };
        124 { ldcr }:
          begin
            getq;
            pshrel(getrel(q))
          end;
          7 { ldcs }:
          begin
            getq;
            getset(q, s1);
            pshset(s1)
          end;

          9 { indi }:
          begin
            getq;
            popadr(ad);
            pshint(getint(ad + q))
          end;
        198 { indx }:
          begin
            getq;
            popadr(ad);
            pshint(getbyt(ad + q))
          end;
         85 { inda }:
          begin
            getq;
            popadr(ad);
            ad1 := getadr(ad + q);
            pshadr(ad1)
          end;
         86 { indr }:
          begin
            getq;
            popadr(ad);
            pshrel(getrel(ad + q))
          end;
         87 { inds }:
          begin
            getq;
            popadr(ad);
            getset(ad + q, s1);
            pshset(s1)
          end;
         88 { indb }:
          begin
            getq;
            popadr(ad);
            pshint(Ord(getbol(ad + q)))
          end;
         89 { indc }:
          begin
            getq;
            popadr(ad);
            pshint(Ord(getchr(ad + q)))
          end;

         93 { incb },
         94 { incc },
        201 { incx },
         10 { inci }:
          begin
            getq;
            popint(i1);
            if dochkovf then
              if (i1 < 0) = (q < 0) then
                if maxint - Abs(i1) < Abs(q) then
                  errori('Arithmetic overflow      ');
            pshint(i1 + q)
          end;
         90 { inca }:
          begin
            getq;
            popadr(a1);
            pshadr(a1 + q)
          end;

         11 { mst }:
          begin
            { p=level of calling procedure minus level of called
              procedure + 1;  set dl and sl, decrement sp }
            { then length of this element is
              max(intsize, realsize, boolsize, charsize, ptrsize }
            getp;
            getq;
            { allocate function result as zeros }
            for j := 1 to q div intsize do
              pshint(0);
            { invalidate }
            for j := 1 to q do
              putdef(sp + j - 1, False);
            ad := sp; { save mark base }
            { allocate mark as zeros }
            for j := 1 to marksize div intsize do
              pshint(0);

            { mark function result invalid }
            { for j := 0 to maxresult-1 do putdef(ad+markfv+j, False); }

            putadr(ad + marksl, base(p)); { sl }
            { the length of this element is ptrsize }
            putadr(ad + markdl, mp); { dl }
            { idem }
            putadr(ad + markep, ep) { ep }
          end;

         12 { cup }:
          begin { p=no of locations for parameters, q=entry point }
            getp;
            getq;
            mp := sp + (p + marksize); { mp to base of mark }
            putadr(mp + markra, pc); { place ra }
            pc := q
          end;

         13 { ents }:
          begin
            getq;
            ad := mp + q; { q = length of dataseg }
            if ad <= np then
            begin
              errori('Store overflow: ents     ');
            end;
            { clear allocated memory and set undefined }
            while sp > ad do
            begin
              sp := sp - 1;
              store[sp] := 0;
              putdef(sp, False);
            end;
            putadr(mp + marksb, sp) { set bottom of stack }
          end;

        173 { ente }:
          begin
            getq;
            ep := sp + q;
            if ep <= np then
              errori('Store overflow: ente     ');
            putadr(mp + market, ep); { place current ep }
            putint(ad + markwb, wthcnt) { with base count }
          end;
        { q = max space required on stack }

        { For characters and booleans, need to clean 8 bit results because
        only the lower 8 bits were stored to. }
        130 { retc }:
          begin
            { set stack below function result }
            sp := mp;
            putint(sp, Ord(getchr(sp)));
            pc := getadr(mp + markra);
            ep := getadr(mp + markep);
            mp := getadr(mp + markdl)
          end;
        131 { retb }:
          begin
            { set stack below function result }
            sp := mp;
            putint(sp, Ord(getbol(sp)));
            pc := getadr(mp + markra);
            ep := getadr(mp + markep);
            mp := getadr(mp + markdl)
          end;
         14 { retp },
        128 { reti },
        204 { retx },
        129 { retr },
        132 { reta }:
          begin
            { set stack below function result, if any }
            sp := mp;
            pc := getadr(mp + markra);
            ep := getadr(mp + markep);
            mp := getadr(mp + markdl)
          end;

         15 { csp }:
          begin
            q := store[pc];
            pc := pc + 1;
            callsp
          end;

         16 { ixa }:
          begin
            getq;
            popint(i);
            popadr(a1);
            pshadr(q * i + a1)
          end;

         17 { equa }:
          begin
            popadr(a2);
            popadr(a1);
            pshint(Ord(a1 = a2))
          end;
        139 { equb },
        141 { equc },
        137 { equi }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 = i2))
          end;
        138 { equr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 = r2))
          end;
        140 { equs }:
          begin
            popset(s2);
            popset(s1);
            pshint(Ord(s1 = s2))
          end;
        142 { equm }:
          begin
            getq;
            compare;
            pshint(Ord(b))
          end;

        18 { neqa }:
          begin
            popadr(a2);
            popadr(a1);
            pshint(Ord(a1 <> a2))
          end;
        145 { neqb },
        147 { neqc },
        143 { neqi }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 <> i2))
          end;
        144 { neqr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 <> r2))
          end;
        146 { neqs }:
          begin
            popset(s2);
            popset(s1);
            pshint(Ord(s1 <> s2))
          end;
        148 { neqm }:
          begin
            getq;
            compare;
            pshint(Ord(not b))
          end;

        151 { geqb },
        153 { geqc },
        149 { geqi }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 >= i2))
          end;
        150 { geqr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 >= r2))
          end;
        152 { geqs }:
          begin
            popset(s2);
            popset(s1);
            pshint(Ord(s1 >= s2))
          end;
        154 { geqm }:
          begin
            getq;
            compare;
            pshint(Ord(b or (store[a1 + i] >= store[a2 + i])))
          end;

        157 { grtb },
        159 { grtc },
        155 { grti }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 > i2))
          end;
        156 { grtr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 > r2))
          end;
        158 { grts }: errori('set inclusion            ');
        160 { grtm }:
          begin
            getq;
            compare;
            pshint(Ord(not b and (store[a1 + i] > store[a2 + i])))
          end;

        163 { leqb },
        165 { leqc },
        161 { leqi }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 <= i2))
          end;
        162 { leqr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 <= r2))
          end;
        164 { leqs }:
          begin
            popset(s2);
            popset(s1);
            pshint(Ord(s1 <= s2))
          end;
        166 { leqm }:
          begin
            getq;
            compare;
            pshint(Ord(b or (store[a1 + i] <= store[a2 + i])))
          end;

        169 { lesb },
        171 { lesc },
        167 { lesi }:
          begin
            popint(i2);
            popint(i1);
            pshint(Ord(i1 < i2))
          end;
        168 { lesr }:
          begin
            poprel(r2);
            poprel(r1);
            pshint(Ord(r1 < r2))
          end;
        170 { less }: errori('Set inclusion            ');
        172 { lesm }:
          begin
            getq;
            compare;
            pshint(Ord(not b and (store[a1 + i] < store[a2 + i])))
          end;

         23 { ujp }:
          begin
            getq;
            pc := q
          end;
         24 { fjp }:
          begin
            getq;
            popint(i);
            if i = 0 then
              pc := q
          end;
         25 { xjp }:
          begin
            getq;
            popint(i1);
            pc := i1 * ujplen + q
          end;

         95 { chka },
        190 { ckla }:
          begin
            getq;
            popadr(a1);
            pshadr(a1);
            {     0 = assign pointer including nil
              Not 0 = assign pointer from heap address }
            if a1 = 0 then
              { if zero, but not nil, it's never been assigned }
              errori('Uninitialized pointer    ')
            else if (q <> 0) and (a1 = nilval) then
              { q <> 0 means deref, and it was nil
                (which is not zero) }
              errori('Dereference of nil ptr   ')
            else if ((a1 < gbtop) or (a1 >= np)) and
              (a1 <> nilval) then
              { outside heap space (which could have
                contracted!) }
              errori('Bad pointer value        ')
            else if dochkrpt and (a1 <> nilval) then
            begin
              { perform use of freed space check }
              if isfree(a1) then
                { attempt to dereference or assign a freed
                  block }
                errori('Ptr used after dispose op')
            end
          end;
         97 { chks }:
          begin
            getq;
            popset(s1);
            pshset(s1);
            for j := setlow to getint(q) - 1 do
              if j in s1 then
                errori('Set element out of range ');
            for j := getint(q + intsize) + 1 to sethigh do
              if j in s1 then
                errori('Set element out of range ');
          end;
         98 { chkb },
         99 { chkc },
        199 { chkx },
         26 { chki }:
          begin
            getq;
            popint(i1);
            pshint(i1);
            if (i1 < getint(q)) or (i1 > getint(q + intsize)) then
              errori('Value out of range       ')
          end;

        187 { cks }: pshint(0);
        175 { ckvi },
        203 { ckvx },
        179 { ckvb },
        180 { ckvc }:
          begin
            getq;
            popint(i2);
            popint(i1);
            pshint(i1);
            pshint(Ord((i1 = q) or (i2 <> 0)));
          end;
        188 { cke }:
          begin
            popint(i2);
            popint(i1);
            if i2 = 0 then
              errori('Variant not active       ')
          end;

        { all the dups are defined, but not all used }
        185 { dupb },
        186 { dupc },
        181 { dupi }:
          begin
            popint(i1);
            pshint(i1);
            pshint(i1)
          end;
        182 { dupa }:
          begin
            popadr(a1);
            pshadr(a1);
            pshadr(a1)
          end;
        183 { dupr }:
          begin
            poprel(r1);
            pshrel(r1);
            pshrel(r1)
          end;
        184 { dups }:
          begin
            popset(s1);
            pshset(s1);
            pshset(s1)
          end;

        189 { inv }:
          begin
            popadr(ad);
            putdef(ad, False)
          end;

         28 { adi }:
          begin
            popint(i2);
            popint(i1);
            if dochkovf then
              if (i1 < 0) = (i2 < 0) then
                if maxint - Abs(i1) < Abs(i2) then
                  errori('Arithmetic overflow      ');
            pshint(i1 + i2)
          end;
         29 { adr }:
          begin
            poprel(r2);
            poprel(r1);
            pshrel(r1 + r2)
          end;
         30 { sbi }:
          begin
            popint(i2);
            popint(i1);
            if dochkovf then
              if (i1 < 0) <> (i2 < 0) then
                if maxint - Abs(i1) < Abs(i2) then
                  errori('Arithmetic overflow      ');
            pshint(i1 - i2)
          end;
         31 { sbr }:
          begin
            poprel(r2);
            poprel(r1);
            pshrel(r1 - r2)
          end;
         32 { sgs }:
          begin
            popint(i1);
            if (i1 < setlow) or (i1 > sethigh) then
              errori('Set element out of range ');
            pshset([i1])
          end;
         33 { flt }:
          begin
            popint(i1);
            pshrel(i1)
          end;

        { note that flo implies the tos is float as well }
         34 { flo }:
          begin
            poprel(r1);
            popint(i1);
            pshrel(i1);
            pshrel(r1)
          end;

         35 { trc }:
          begin
            poprel(r1);
            if dochkovf then
              if (r1 < -maxint) or (r1 > maxint) then
                errori('Real argument to large   ');
            pshint(trunc(r1))
          end;
         36 { ngi }:
          begin
            popint(i1);
            pshint(-i1)
          end;
         37 { ngr }:
          begin
            poprel(r1);
            pshrel(-r1)
          end;
         38 { sqi }:
          begin
            popint(i1);
            if dochkovf then
              if i1 <> 0 then
                if Abs(i1) > maxint div Abs(i1) then
                  errori('Arithmetic overflow      ');
            pshint(Sqr(i1))
          end;
         39 { sqr }:
          begin
            poprel(r1);
            pshrel(Sqr(r1))
          end;
         40 { abi }:
          begin
            popint(i1);
            pshint(Abs(i1))
          end;
         41 { abr }:
          begin
            poprel(r1);
            pshrel(Abs(r1))
          end;
         42 { not }:
          begin
            popint(i1);
            b1 := i1 <> 0;
            pshint(Ord(not b1))
          end;
         43 { and }:
          begin
            popint(i2);
            b2 := i2 <> 0;
            popint(i1);
            b1 := i1 <> 0;
            pshint(Ord(b1 and b2))
          end;
         44 { ior }:
          begin
            popint(i2);
            b2 := i2 <> 0;
            popint(i1);
            b1 := i1 <> 0;
            pshint(Ord(b1 or b2))
          end;
         45 { dif }:
          begin
            popset(s2);
            popset(s1);
            pshset(s1 - s2)
          end;
         46 { int }:
          begin
            popset(s2);
            popset(s1);
            pshset(s1 * s2)
          end;
         47 { uni }:
          begin
            popset(s2);
            popset(s1);
            pshset(s1 + s2)
          end;
         48 { inn }:
          begin
            popset(s1);
            popint(i1);
            pshint(Ord(i1 in s1))
          end;
         49 { mod }:
          begin
            popint(i2);
            popint(i1);
            if dochkovf then
              if i2 <= 0 then
                errori('Invalid divisor in mod   ');
            pshint(Mod2(i1, i2))
          end;
         50 { odd }:
          begin
            popint(i1);
            pshint(Ord(Odd(i1)))
          end;
         51 { mpi }:
          begin
            popint(i2);
            popint(i1);
            if dochkovf then
              if (i1 <> 0) and (i2 <> 0) then
                if Abs(i1) > maxint div Abs(i2) then
                  errori('Arithmetic overflow      ');
            pshint(i1 * i2)
          end;
         52 { mpr }:
          begin
            poprel(r2);
            poprel(r1);
            pshrel(r1 * r2)
          end;
         53 { dvi }:
          begin
            popint(i2);
            popint(i1);
            if dochkovf then
              if i2 = 0 then
                errori('Zero divide              ');
            pshint(i1 div i2)
          end;
         54 { dvr }:
          begin
            poprel(r2);
            poprel(r1);
            if dochkovf then
              if r2 = 0.0 then
                errori('Zero divide              ');
            pshrel(r1 / r2)
          end;
         55 { mov }:
          begin
            getq;
            popint(i2);
            popint(i1);
            for i3 := 0 to q - 1 do
            begin
              store[i1 + i3] := store[i2 + i3];
              putdef(i1 + i3, getdef(i2 + i3))
            end;
            { q is a number of storage units }
          end;
         56 { lca }:
          begin
            getq;
            pshadr(q)
          end;

        103 { decb },
        104 { decc },
        202 { decx },
         57 { deci }:
          begin
            getq;
            popint(i1);
            if dochkovf then
              if (i1 < 0) <> (q < 0) then
                if maxint - Abs(i1) < Abs(q) then
                  errori('Arithmetic overflow      ');
            pshint(i1 - q)
          end;

         58 { stp }: interpreting := False;

        134 { ordb },
        136 { ordc },
        200 { ordx },
         59 { ordi }:
          ; { ord is a no-op }

         60 { chr }:
          ; { chr is a no-op }

         61 { ujc }:
          errori('Case - error             ');
         62 { rnd }:
          begin
            poprel(r1);
            if dochkovf then
              if (r1 < -(maxint + 0.5)) or (r1 > maxint + 0.5) then
                errori('Real argument to large   ');
            pshint(round(r1))
          end;
         63 { pck }:
          begin
            getq;
            getq1;
            popadr(a3);
            popadr(a2);
            popadr(a1);
            if a2 + q > q1 then
              errori('Pack elements out of bnds');
            for i4 := 0 to q - 1 do
            begin
              chkdef(a1 + a2);
              store[a3 + i4] := store[a1 + a2];
              putdef(a3 + i4, getdef(a1 + a2));
              a2 := a2 + 1
            end
          end;
         64 { upk }:
          begin
            getq;
            getq1;
            popadr(a3);
            popadr(a2);
            popadr(a1);
            if a3 + q > q1 then
              errori('Unpack elem out of bnds  ');
            for i4 := 0 to q - 1 do
            begin
              chkdef(a1 + i4);
              store[a2 + a3] := store[a1 + i4];
              putdef(a2 + a3, getdef(a1 + i4));
              a3 := a3 + 1
            end
          end;

        110 { rgs }:
          begin
            popint(i2);
            popint(i1);
            if (i1 < setlow) or (i1 > sethigh) or
              (i2 < setlow) or (i2 > sethigh) then
              errori('Set element out of range ');
            pshset([i1..i2])
          end;
        112 { ipj }:
          begin
            getp;
            getq;
            pc := q;
            mp := base(p); { index the mark to restore }
            { restore marks until we reach the destination level }
            sp := getadr(mp + marksb); { get the stack bottom }
            ep := getadr(mp + market); { get the mark ep }
            i := getint(mp + markwb); { get the with base count }
            while wthcnt <> i do
              withexit { clean the with stack }
          end;
        113 { cip }:
          begin
            getp;
            popadr(ad);
            mp := sp + (p + marksize);
            { replace next link mp with the one for the target }
            putadr(mp + marksl, getadr(ad + 1 * ptrsize));
            putadr(mp + markra, pc);
            pc := getadr(ad)
          end;
        114 { lpa }:
          begin
            getp;
            getq; { place procedure address on stack }
            pshadr(base(p));
            pshadr(q)
          end;
        117 { dmp }:
          begin
            getq;
            sp := sp + q
          end; { remove top of stack }

        118 { swp }:
          begin
            getq;
            swpstk(q)
          end;

        119 { tjp }:
          begin
            getq;
            popint(i);
            if i <> 0 then
              pc := q
          end;

        120 { lip }:
          begin
            getp;
            getq;
            ad := base(p) + q;
            ad1 := getadr(ad);
            ad2 := getadr(ad + 1 * ptrsize);
            pshadr(ad2);
            pshadr(ad1);
          end;

        191 { cta }:
          begin
            getq;
            getq1;
            getq2;
            popint(i);
            popadr(ad);
            pshadr(ad);
            pshint(i);
            ad := ad - q - intsize;
            ad1 := getadr(ad);
            if ad1 < intsize then
              errori('System error             ');
            ad1 := ad1 - adrsize - 1;
            ad := ad - ad1 * intsize;
            i := i - getint(q2 + intsize);
            if ad1 >= q1 then
            begin
              if (i < 0) or (i >= getint(q2)) then
                errori('Value out of range       ');
              if getadr(ad + (q1 - 1) * intsize) <>
                getint(q2 + (i + 2) * intsize) then
                errori('Change to alloc tagfield ');
            end
          end;

        192 { ivti },
         91 { ivtx },
         92 { ivtb },
         96 { ivtc }:
          begin
            getq;
            getq1;
            getq2;
            popint(i);
            popadr(ad);
            pshadr(ad);
            pshint(i);
            i := i - getint(q2 + intsize);
            if (i < 0) or (i >= getint(q2)) then
              errori('Value out of range       ');
            if dochkdef then
            begin
              b := getdef(ad);
              if b then
              begin
                if op = 192 then
                  j := getint(ad)
                else
                  j := getbyt(ad);
                j := j - getint(q2 + intsize);
                b := getint(q2 + (i + 2) * intsize) <>
                  getint(q2 + (j + 2) * intsize);
              end;
              if b then
              begin
                ad := ad + q;
                for j := 1 to q1 do
                begin
                  putdef(ad, False);
                  ad := ad + 1
                end
              end
            end
          end;

        174 { mrkl }:
          begin
            getq;
            srclin := q;
            if dotrcsrc then
              Writeln('Source line executed: ', q: 1)
          end;
         19 { vbs }:
          begin
            getq;
            popadr(ad);
            varenter(ad, ad + q - 1)
          end;
         20 { vbe }:
           varexit;

          8 { cvbi },
         21 { cvbx },
         22 { cvbb },
         27 { cvbc }:
          begin
            getq;
            getq1;
            getq2;
            popint(i);
            popadr(ad);
            pshadr(ad);
            pshint(i);
            i := i - getint(q2 + intsize);
            if (i < 0) or (i >= getint(q2)) then
              errori('Value out of range       ');
            b := getdef(ad);
            if b then
            begin
              if op = 8 then
                j := getint(ad)
              else
                j := getbyt(ad);
              j := j - getint(q2 + intsize);
              b := getint(q2 + (i + 2) * intsize) <>
                getint(q2 + (j + 2) * intsize)
            end;
            if b then
            begin
              ad := ad + q;
              if varlap(ad, ad + q1 - 1) then
                errori('Change to VAR ref variant');
            end
          end;
        100 { ctp }:
          begin
            popadr(ad);
            pshadr(ad);
            ad := ad - intsize;
            ad1 := getadr(ad);
            if ad1 < intsize then
              errori('System error             ');
            ad1 := ad1 - adrsize - 1;
            if ad1 <> 0 then
              errori('Access tag allocated rec ')
          end;
        101 { wbs }:
          begin
            popadr(ad);
            pshadr(ad);
            withenter(ad)
          end;
        102 { wbe }:
          withexit;

        { illegal instructions }
        111, 115, 116, 121, 122, 133, 135, 176, 177, 178, 205, 206, 207, 208,
        209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222,
        223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236,
        237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250,
        251, 252, 253, 254, 255:
          errori('Illegal instruction      ');
      end
    end; { while interpreting }

    if varlst <> nil then
      errori('VAR block imbalance      ');
    if wthlst <> nil then
      errori('With block imbalance     ');

    { perform heap dump if requested }
    if dodmpspc then
      repspc;

  except
    on E: EAbort do
      ;
  end;

  Writeln;
  Writeln('program complete');

  for i := 5 to maxfil do
  begin
    if TtextRec(filtable[i]).Handle <> 0 then
    begin
      if filstate[i] = fwrite then
      begin
        AddEoln(filtable[i]);
        Flush(filtable[i]);
      end;
      CloseFile(filtable[i]);
    end;
    if TFileRec(bfiltable[i]).Handle <> 0 then
      CloseFile(bfiltable[i]);
  end;

  CloseFile(prd);
  Flush(prr);
  CloseFile(prr);

  RemoveTempFile;
end.

