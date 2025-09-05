A grammar is a set of rules that let us define a language. These are called **production rules** and can be derived into many different tools. One of them is **String Rewriting Systems** (also called Semi-Thue Systems or Markov Algorithms). Ignoring technical details, they are a set of rules that substitute ocurrences in a given string by other strings. 

The rules have the following format:

```
str1 -> str2
```

We define a rule application as the substitution of a substring following a rule. If this substring appears more than once, only one of this occurences is substituted and any of them is equally valid as an option:

```python
'a' -> 'c' # Substitution rule

'aba' # Base string
'cba' # One application on position 0
'abc' # One application on position 2
'cbc' # Two applications
```

Another valid example of rule application would be the following:

```python
# Rules
'l' -> 'de'
'm' -> 'col'
'rr' -> 'wakr'
'akr' -> 'ars'

# Application
'mrr' # Starting string
'colrr' # Second rule
'coderr' # First rule
'codewakr' # Third rule
'codewars' # Last rule 
```
Note that this example is exhaustive, but Semi-Thue Systems can be potentially infinite:

```python
# Rules
'a' -> 'aa'

# Application
'a' # Starting string
'aa' # First application
'aaa' # Second application
...
```

The so called **Word Problem** is to decide whether or not a string can be derived from another using these rules. This is an **undecidable problem**, but if we restrict it to a certain number of applications, we can give it a solution.

Your task is to write a function that solves the word problem given a maximum number of rule applications. 

**Python:** The rules are given as tuples where the left and the right handside of the rule correspond to the first and the second element respectively.

**Notes:** 
* Two rules can have the same left handside and a different right handside.
* You do not have to worry too much about performance yet. A simple, funtional answer will be enough.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded