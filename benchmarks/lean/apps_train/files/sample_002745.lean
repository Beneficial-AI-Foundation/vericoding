# Convert a linked list to a string

## Related Kata

Although this Kata is not part of an official Series, you may also want to try out [Parse a linked list from a string](https://www.codewars.com/kata/582c5382f000e535100001a7) if you enjoyed this Kata.

## Preloaded

Preloaded for you is a class, struct or derived data type `Node` (depending on the language) used to construct linked lists in this Kata:

```python
class Node():
    def __init__(self, data, next = None):
        self.data = data
        self.next = next
```

~~~if:objc
*NOTE: In Objective-C, the* `Node` *struct is placed on top of your main solution because there is a "double-import" bug in the Preloaded section at the time of writing (which cannot be fixed on my end).  Attempts to modify it (e.g. to cheat the tests in some way) will likely result in a test crash so it is not recommended for you to modify that section ;)*
~~~

~~~if:c
*NOTE: In C, the* `Node` *struct is placed on top of your main solution (and the [Sample] Test Cases) because the compiler complains about not recognizing the* `Node` *datatype even after adding it to the Preloaded section.  Attempts to modify it (e.g. to cheat the tests in some way) will likely result in a test crash so it is not recommended for you to modify that section ;)*
~~~

If you are attempting this Kata in NASM then note that the code example shown directly above may not be relevant; please refer to the Sample Tests (written in C) for the exact definition of the `Node` structure.

## Prerequisites

This Kata assumes that you are already familiar with the idea of a linked list.  If you do not know what that is, you may want to read up on [this article on Wikipedia](https://en.wikipedia.org/wiki/Linked_list).  Specifically, the linked lists this Kata is referring to are **singly linked lists**, where the value of a specific node is stored in its `data`/`$data`/`Data` property, the reference to the next node is stored in its `next`/`$next`/`Next`/`next_node` property and the terminator for a list is `null`/`NULL`/`None`/`nil`/`nullptr`/`null()`.

## Task

*If you are attempting this Kata in NASM, the code examples shown below may not be relevant at all - please refer to the Sample Tests (written in C) for the exact requirements.*

Create a function `stringify` which accepts an argument `list`/`$list` and returns a string representation of the list.  The string representation of the list starts with the value of the current `Node`, specified by its `data`/`$data`/`Data` property, followed by a whitespace character, an arrow and another whitespace character (`" -> "`), followed by the rest of the list.  The end of the string representation of a list must always end with `null`/`NULL`/`None`/`nil`/`nullptr`/`null()` (all caps or all lowercase depending on the language you are undertaking this Kata in).  For example, given the following list:

```python
Node(1, Node(2, Node(3)))
```

... its string representation would be:

```python
"1 -> 2 -> 3 -> None"
```

And given the following linked list:

```python
Node(0, Node(1, Node(4, Node(9, Node(16)))))
```

... its string representation would be:

```python
"0 -> 1 -> 4 -> 9 -> 16 -> None"
```

Note that `null`/`NULL`/`None`/`nil`/`nullptr`/`null()` itself is also considered a valid linked list.  In that case, its string representation would simply be `"null"`/`"NULL"`/`"None"`/`"nil"`/`"nullptr"`/`@"NULL"`/`"null()"` (again, depending on the language).

For the simplicity of this Kata, you may assume that any `Node` in this Kata may only contain **non-negative integer** values.  For example, you will not encounter a `Node` whose `data`/`$data`/`Data` property is `"Hello World"`.

Enjoy, and don't forget to check out my other Kata Series :D

~~~if:fortran
*NOTE: In Fortran, your returned string is* **not** *permitted to contain any leading and/or trailing whitespace.*
~~~

def stringify {α : Type} [ToString α] : Node α → String :=
  sorry

def make_linked_list {α : Type} : List α → Node α :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
