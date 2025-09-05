```if:javascript
`Array.prototype.length` will give you the number of top-level elements in an array.
```
```if:ruby
`Array#length` will give you the number of top-level elements in an array.
```
```if:csharp
The `Length` property of an array will give you the number of top-level elements in an array.
```
```if:php
`count()` will give you the number of top-level elements in an array if exactly one argument `$a` is passed in which is the array.
```
```if:python
`len(a)` will give you the number of top-level elements in the list/array named `a`.
```

Your task is to create a function ```deepCount``` that returns the number of ALL elements within an array, including any within inner-level arrays.

For example:

```if:javascript
    deepCount([1, 2, 3]);  
    //>>>>> 3
    deepCount(["x", "y", ["z"]]);  
    //>>>>> 4
    deepCount([1, 2, [3, 4, [5]]]);  
    //>>>>> 7
```
```if:ruby
    deepCount([1, 2, 3]);  
    //>>>>> 3
    deepCount(["x", "y", ["z"]]);  
    //>>>>> 4
    deepCount([1, 2, [3, 4, [5]]]);  
    //>>>>> 7
```
```if:csharp
    deepCount([1, 2, 3]);  
    //>>>>> 3
    deepCount(["x", "y", ["z"]]);  
    //>>>>> 4
    deepCount([1, 2, [3, 4, [5]]]);  
    //>>>>> 7
```
```if:php
    deep_c([1, 2, 3]);
    //>>>>> 3
    deep_c(["x", "y", ["z"]]);
    //>>>>> 4
    deep_c([1, 2, [3, 4, [5]]]);
    //>>>>> 7
```
```if:python
    deepCount([1, 2, 3]);  
    //>>>>> 3
    deepCount(["x", "y", ["z"]]);  
    //>>>>> 4
    deepCount([1, 2, [3, 4, [5]]]);  
    //>>>>> 7
```

The input will always be an array.

```if:php
In PHP you may *not* assume that the array passed in will be non-associative.

Please note that `count()`, `eval()` and `COUNT_RECURSIVE` are disallowed - you should be able to implement the logic for `deep_c()` yourself ;)
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
