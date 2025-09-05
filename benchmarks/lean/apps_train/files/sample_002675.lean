##Task:

You have to write a function **pattern** which creates the following pattern upto n number of rows. 

* If the Argument is 0 or a Negative Integer then it should return "" i.e. empty string.

* If any odd number is passed as argument then the pattern should last upto the largest even number which is smaller than the passed odd number.

* If the argument is 1 then also it should return "".

##Examples:

pattern(8):

    22
    4444
    666666
    88888888

pattern(5):

    22
    4444

```Note: There are no spaces in the pattern```

```Hint: Use \n in string to jump to next line```

def pattern (n : Int) : String := sorry

def String.lines (s : String) : List String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded