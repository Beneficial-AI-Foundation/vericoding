Create a method (**JS**: function) `every` which returns every nth element of an array.

### Usage

With no arguments, `array.every` it returns every element of the array.  
With one argument, `array.every(interval)` it returns every `interval`th element.  
With two arguments, `array.every(interval, start_index)` it returns every `interval`th element starting at index `start_index` 

**Note**: due to fact JS translation ask for a function instead of an Array method the above uses will be :
```
javascript:                          ruby:
every(array)                         array.every
every(array, interval)               array.every(interval)
every(array, interval, start_index)  array.every(interval, start_index)

```

### Examples

### Notes
Test cases:  

`interval` will always be a positive integer (but may be larger than the size of the array).  
`start_index` will always be within the bounds of the array.  

Once you have completed this kata, try the **advanced version** (http://www.codewars.com/kata/every-nth-array-element-advanced) which allows negative intervals and unbounded start\_indexes 

### Translator notes
Ruby is the original language for this kata.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
