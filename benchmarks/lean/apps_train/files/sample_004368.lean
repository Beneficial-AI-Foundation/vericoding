Math hasn't always been your best subject, and these programming symbols always trip you up!

I mean, does `**` mean *"Times, Times"* or *"To the power of"*?

Luckily, you can create the function `expression_out()` to write out the expressions for you!

The operators you'll need to use are:

```python
{ '+':   'Plus ',
  '-':   'Minus ',
  '*':   'Times ',
  '/':   'Divided By ',  
  '**':  'To The Power Of ',
  '=':   'Equals ',
  '!=':  'Does Not Equal ' }
```

These values will be stored in the preloaded dictionary `OPERATORS` just as shown above.

But keep in mind: INVALID operators will also be tested, to which you should return `"That's not an operator!"`

And all of the numbers will be `1` to`10`!
Isn't that nice!

Here's a few examples to clarify:

```python
expression_out("4 ** 9") == "Four To The Power Of Nine"
expression_out("10 - 5") == "Ten Minus Five"
expression_out("2 = 2")  == "Two Equals Two"
```

Good luck!

def expression_out (expr : String) : String := sorry

def VALID_OPERATORS : List String := ["+", "-", "*", "/", "**", "=", "!="]

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded