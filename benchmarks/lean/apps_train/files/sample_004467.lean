Write a function ```convert_temp(temp, from_scale, to_scale)``` converting temperature from one scale to another. 
Return converted temp value. 

Round converted temp value to an integer(!).

Reading: http://en.wikipedia.org/wiki/Conversion_of_units_of_temperature

```
possible scale inputs:
    "C"  for Celsius
    "F"  for Fahrenheit
    "K"  for Kelvin
    "R"  for Rankine
    "De" for Delisle
    "N"  for Newton
    "Re" for Réaumur
    "Ro" for Rømer
```

```temp``` is a number, ```from_scale``` and ```to_scale``` are strings. 

```python
convert_temp(   100, "C",  "F") # => 212
convert_temp(    40, "Re", "C") # => 50
convert_temp(    60, "De", "F") # => 140
convert_temp(373.15, "K",  "N") # => 33
convert_temp(   666, "K",  "K") # => 666
```

def convert_temp (temp : Float) (from_scale : String) (to_scale : String) : Int :=
  sorry

def round (x : Float) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded