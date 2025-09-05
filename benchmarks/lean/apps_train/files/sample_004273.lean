Create a function that accepts 3 inputs, a string, a starting location, and a length.  The function needs to simulate the string endlessly repeating in both directions and return a substring beginning at the starting location and continues for length.

Example:
```python
endless_string('xyz', -23, 6) == 'yzxyzx'
```
To visualize:

           Negative                               Positive
    3         2         1         *         1         2         3      
    0987654321098765432109876543210123456789012345678901234567890
    xyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzxyzx
           ******
         -23 for a length of 6 == 'yzxyzx'

Some more examples:
```python
endless_string('xyz', 0, 4) == 'xyzx'
endless_string('xyz', 19, 2) == 'yz'
endless_string('xyz', -4, -4) == 'zxyz'
```

A negative length needs to include the starting postion and return the characters to the left of the starting position.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
