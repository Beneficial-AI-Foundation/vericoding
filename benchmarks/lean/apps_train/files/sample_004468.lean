# Challenge : 

Write a function that takes a single argument `n` that is a string representation of a simple mathematical expression and evaluates it as a floating point value. 

# Commands : 
- positive or negative decimal numbers
- `+, -, *, /, ( / ).`

---

Expressions use [infix notation](https://en.wikipedia.org/wiki/Infix_notation). 

# Evaluation : 

Operators should be evaluated in the order they appear and not as in `BODMAS`, though brackets __should__ be correctly observed. 

The function should return the correct result for any possible expression of this form.

# Note : 

- All given input will be valid.
- It will consist entirely of numbers or one of the operators.
- Parentheses will alway be matched.
- Use of `eval` or its equivalent is forbidden
- use of `exec` is forbidden (Python) 
- Use of `Function` or any of their (Function, eval) equivalent is also forbidden.
- Using `require` is also forbidden. (`import` for python)
- Using more than 7 (8 for python) lines is also forbidden.
- Using more than 260 (JS) / 240 (python) characters is also forbidden.
- Having more than 100 chars per line is forbidden.
- Having more than 6 semi-colons is forbidden

and that is about it.

--- 

# Examples : 

    e("2*3*4*5+99")               ---> 219
    e("2*3*4*5+99*321-12312312")  ---> -12242013
    e("1-2*2/2*2-1*7+3")          ---> -18

---

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded