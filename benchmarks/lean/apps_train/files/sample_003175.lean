## Task:
You have to write a function `pattern` which returns the following Pattern(See Pattern & Examples) upto `n` number of rows. 

* Note:`Returning` the pattern is not the same as `Printing` the pattern.

#### Rules/Note:
* If `n < 1` then it should return "" i.e. empty string.
* There are `no whitespaces` in the pattern.

### Pattern: 

    1
    22
    333
    ....
    .....
    nnnnnn

### Examples:

+ pattern(5):

      1
      22
      333
      4444
      55555

* pattern(11):  

      1
      22
      333
      4444
      55555
      666666
      7777777
      88888888
      999999999
      10101010101010101010
      1111111111111111111111

```if-not:cfml
* Hint: Use \n in string to jump to next line
```
```if:cfml
* Hint: Use Chr(10) in string to jump to next line
```
[List of all my katas]('http://www.codewars.com/users/curious_db97/authored')

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
