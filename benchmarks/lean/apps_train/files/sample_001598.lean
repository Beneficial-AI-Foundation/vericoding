This kata is  blatantly copied from  inspired by This Kata
Welcome

this is the second in the series of the string iterations kata!

Here we go!

---------------------------------------------------------------------------------

We have a string s

Let's say you start with this: "String"

The first thing you do is reverse it: "gnirtS"

Then you will take the string from the 1st position and reverse it again: "gStrin"

Then you will take the string from the 2nd position and reverse it again: "gSnirt"

Then you will take the string from the 3rd position and reverse it again: "gSntri"

Continue this pattern until you have done every single position, and then you will return the string you have created. For this particular string, you would return: 
"gSntir"

now,

The Task:

In this kata, we also have a number x

take that reversal function, and apply it to the string x times.

return the result of the string after applying the reversal function to it x times.

    example where s = "String" and x = 3:

    after 0 iteration  s = "String"
    after 1 iteration  s = "gSntir"
    after 2 iterations s = "rgiStn"
    after 3 iterations s = "nrtgSi"

    so you would return "nrtgSi".

 Note 

String lengths may exceed 2 million

x exceeds a billion

be read to optimize

if this is too hard, go here https://www.codewars.com/kata/string-%3E-n-iterations-%3E-string/java

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded