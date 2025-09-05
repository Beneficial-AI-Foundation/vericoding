We like parsed SQL or PL/SQL blocks...

You need to write function that return list of literals indices from source block, excluding "in" comments, OR return empty list if no literals found.

input:
some fragment of sql or pl/sql code

output:
list of literals indices [(start, end), ...] OR empty list

Sample:
```
get_textliterals("'this' is sample") -> [(0,6)]
get_textliterals("'this' is sample 'too'") -> [(0, 6), (15, 20)]
```

Text literal: any text between single quotes
Sample:
```
  s := 'i am literal'
```
Single-line comment: any text started with "--" 
Sample:
```
  a := 1;
  -- this is single-line comment
```
Multy-line comment: any text between /* */
```
  a := 1;
  /*
  this is long multy-line comment
  */
```

Note: 
1) handle single quote inside literal
```
  s := 'we can use quote '' in literal'
```  
2) multy-line literal
```
 s := '
 this is literal too
 ';
```
3) skip literal inside comment
```
s := 'test'; --when comment started - this is not 'literal'
```
4) any unclosed literal should be closed with last symbol of the source fragment
```
s := 'test
```
There is one literal in this code: "'test"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
