Your task in this kata is to implement the function `create_number_class` which will take a string parameter `alphabet` and return a class representing a number composed of this alphabet.

The class number will implement the four classical arithmetic operations (`+`, `-`, `*`, `//`), a method to convert itself to string, and a `convert_to` method which will take another class number as parameter and will return the value of the actual class number converted to the equivalent value with tha alphabet of the parameter class (return a new instance of this one).

Example:

```python
BinClass = create_number_class('01')
HexClass = create_number_class('0123456789ABCDEF')

x = BinClass('1010')
y = BinClass('10')

print(x+y)                   => '1100'
isinstance(x+y, BinClass)    => True
print(x.convert_to(HexClass) => 'A'
```

___Notes:___

* Only positives integers will be used (either as parameters or results of calculations).
* You'll never encounter invalid calculations (divisions by zero or things like that).
* Alphabets will contain at least 2 characters.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
