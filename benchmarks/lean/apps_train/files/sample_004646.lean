Linked lists are data structures composed of nested or chained objects, each containing a single value and a reference to the next object. 

Here's an example of a list:

```python
class LinkedList:
    def __init__(self, value=0, next=None):
        self.value = value
        self.next = next

LinkedList(1, LinkedList(2, LinkedList(3)))

```

Write a function listToArray (or list\_to\_array in Python) that converts a list to an array, like this:

```
[1, 2, 3]
```

Assume all inputs are valid lists with at least one value. For the purpose of simplicity, all values will be either numbers, strings, or Booleans.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded