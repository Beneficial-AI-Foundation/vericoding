The objective is to disambiguate two given names: the original with another

This kata is slightly more evolved than the previous one: [Author Disambiguation: to the point!](https://www.codewars.com/kata/580a429e1cb4028481000019).

The function ```could_be``` is still given the original name and another one to test
against. 

```python
# should return True even with 'light' variations (more details in section below)
> could_be("Chuck Norris", u"chück!")
True

# should False otherwise (whatever you may personnaly think)
> could_be("Chuck Norris", "superman")
False
``` 

**Watch out**: When accents comes into the game, they will enter through **UTF-8 unicodes. **

The function should be tolerant with regards to:

 * upper and lower cases: ```could_be(A, a) : True```
 * accents: ```could_be(E, é) : True```
 * dots: ```could_be(E., E) : True```
 * same for other ending punctuations in [!,;:?]: ```could_be(A, A!) : True```

On the other hand, more consideration needs to be given to *composed names*...
Let's be bold about it: if you have any, they will be considered as a whole :

```python
# We still have:
> could_be("Carlos Ray Norris", "Carlos Ray Norris")
True
> could_be("Carlos-Ray Norris", "Carlos-Ray Norris")
True

# But:
> could_be("Carlos Ray Norris", "Carlos-Ray Norris")
False
> could_be("Carlos-Ray Norris", "Carlos Ray Norris")
False
> could_be("Carlos-Ray Norris", "Carlos Ray-Norris")
False
```

Among the valid combinaisons of the fullname "Carlos Ray Norris", you will find

```python
could_be("Carlos Ray Norris", "carlos ray") : True
could_be("Carlos Ray Norris", "Carlos. Ray, Norris;") : True
could_be("Carlos Ray Norris", u"Carlòs! Norris") : True
```

Too easy ? Try the next step: [Author Disambiguation: Signatures worth it](https://www.codewars.com/kata/author-disambiguation-signatures-worth-it)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
