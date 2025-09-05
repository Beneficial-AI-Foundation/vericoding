The function is not returning the correct values. Can you figure out why?

```python
get_planet_name(3) # should return 'Earth'
```

def validPlanets : Int → Option String
| 1 => some "Mercury"
| 2 => some "Venus"
| 3 => some "Earth"
| 4 => some "Mars"
| 5 => some "Jupiter"
| 6 => some "Saturn"
| 7 => some "Uranus"
| 8 => some "Neptune"
| _ => none

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded