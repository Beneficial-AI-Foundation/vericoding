The objective is to disambiguate two given names: the original with another

Let's start simple, and just work with plain ascii strings. 

The function ```could_be``` is given the original name and another one to test
against. 

```python
# should return True if the other name could be the same person 
> could_be("Chuck Norris", "Chuck")
True

# should False otherwise (whatever you may personnaly think)
> could_be("Chuck Norris", "superman")
False
``` 

Let's say your name is *Carlos Ray Norris*, your objective is to return True if
the other given name matches any combinaison of the original fullname:

```python
could_be("Carlos Ray Norris", "Carlos Ray Norris") : True
could_be("Carlos Ray Norris", "Carlos Ray") : True
could_be("Carlos Ray Norris", "Norris") : True
could_be("Carlos Ray Norris", "Norris Carlos") : True
```

For the sake of simplicity:

 * the function is case sensitive and accent sensitive for now
 * it is also punctuation sensitive
 * an empty other name should not match any original
 * an empty orginal name should not be matchable
 * the function is not symmetrical

The following matches should therefore fail:

```python
could_be("Carlos Ray Norris", " ") : False
could_be("Carlos Ray Norris", "carlos") : False
could_be("Carlos Ray Norris", "Norris!") : False
could_be("Carlos Ray Norris", "Carlos-Ray Norris") : False
could_be("Ray Norris", "Carlos Ray Norris") : False
could_be("Carlos", "Carlos Ray Norris") : False
```

Too easy ? Try the next steps: 

* [Author Disambiguation: a name is a Name!](https://www.codewars.com/kata/author-disambiguation-a-name-is-a-name)
* or even harder: [Author Disambiguation: Signatures worth it](https://www.codewars.com/kata/author-disambiguation-signatures-worth-it)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded