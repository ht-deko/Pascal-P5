# Pascal-P5
P5 Pascal compiler for Delphi.

Pascal-P5 complies with the requirements of level 0 of ISO/IEC 7185.

![image](https://user-images.githubusercontent.com/14885863/149734940-da303252-b089-4ee0-a337-8d3fa69633ee.png)
![image](https://user-images.githubusercontent.com/14885863/149663300-e320f4ce-f4ba-45bc-9771-1442c391f140.png)
![image](https://user-images.githubusercontent.com/14885863/150458903-113e6f5b-42ee-4a42-bff3-a5806e42b7fe.png)
![image](https://user-images.githubusercontent.com/14885863/151692445-7c6a1b13-3916-4122-a893-40b91cad301f.png)

Original version is here:

 - [pascal-p5 (sourceforge.net)](https://sourceforge.net/projects/pascalp5/)
 - [The P5 compiler (standardpascaline.org)](http://www.standardpascaline.org/p5.html)

## Build

You can use Delphi Community Edition to compile.

 - [Delphi Community Edition (Embarcadero)](https://www.embarcadero.com/jp/products/delphi/starter)

## Enhancement

### External file

```pascal
program Test(input, output, TMP='TEMP.TXT');
var
  TMP: text;
begin
  Writeln('Hello, world.');
  Rewrite(TMP);
  Writeln(TMP, 'Hello, world.');
end.
```

### Command-line parameter

```
PCOM [+T | -T] [+L | -L] [+D | -D] [+C | -C] [Pascal file (*.pas)]
PINT [Intermediate file (*.p5)]
```
