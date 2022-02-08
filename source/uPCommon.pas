unit uPCommon;

interface

uses
  System.SysUtils, System.IOUtils;

const
  p5temp     = 'P5TMP';

{ ------------------------------------------------------------------------- }

                           { for Delphi }

{ ------------------------------------------------------------------------- }

procedure AddEoln(var F: Text);
function CurrentChar(var F: Text): WideChar;
procedure Get(var F: Text);
function Mod2(a, n: Integer): Integer;
procedure Page(var F: Text);
procedure RemoveTempFile;
procedure WriteBool(var F: Text; b: Boolean; w: Integer = 0);
procedure WriteReal(var F: Text; r: Real; w: Integer = 0);

implementation

procedure AddEoln(var F: Text);
begin
  if (TTextRec(F).BufPtr + TTextRec(F).BufPos - 1)^ <> #$0A then
    Writeln(F);
end { AddEoln };

function CurrentChar(var F: Text): WideChar;
begin
  Eoln(F);
  Result := WideChar((TTextRec(F).BufPtr + TTextRec(F).BufPos)^);
end { CurrentChar };

{$HINTS OFF}
procedure Get(var F: Text);
var
  ch: Char;
begin
  Read(F, ch);
end { Get };
{$HINTS ON}

function Mod2(a, n: Integer): Integer;
begin
  Result := a - (a div n) * n;
  if Result < 0 then
    Result := Result + n;
end { Mod2 };

procedure Page(var F: Text);
begin
  Write(F, #$0C);
end { Page };

procedure RemoveTempFile;
begin
  for var FileName in TDirectory.GetFiles(TPath.GetTempPath, p5temp + '*.*',
    TSearchOption.soTopDirectoryOnly) do
    try
    TFile.Delete(FileName);
  except
    ;
  end;
end { RemoveTempFile };

procedure WriteBool(var F: Text; b: Boolean; w: Integer = 0);
const
  BOOLSTR: array[Boolean] of string = ('false', 'true');
var
  s: string;
begin
  s := BOOLSTR[b];
  if w > 0 then
  begin
    if Length(s) < w then
      s := StringOfChar(' ', w - (Length(s))) + s
    else
      s := Copy(s, 1, w);
  end;
  Write(F, s);
end { WriteBool };

procedure WriteReal(var F: Text; r: Real; w: Integer = 0);
var
  s: string;
  w2: Integer;
begin
  if w < 8 then
    w2 := 2
  else
    w2 := w - 6;
  s := FloatToStrF(r, ffExponent, w2, 2);
  if r >= 0 then
    s := ' ' + s;
  Write(F, s);
end { WriteReal };

end.
