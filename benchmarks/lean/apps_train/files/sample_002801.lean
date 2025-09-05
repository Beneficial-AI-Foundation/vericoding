__Definition:__ According to Wikipedia, a [complete binary tree](https://en.wikipedia.org/wiki/Binary_tree#Types_of_binary_trees) is a binary tree _"where every level, except possibly the last, is completely filled, and all nodes in the last level are as far left as possible."_

The Wikipedia page referenced above also mentions that _"Binary trees can also be stored in breadth-first order as an implicit data structure in arrays, and if the tree is a complete binary tree, this method wastes no space."_

Your task is to write a method (or function) that takes an array (or list, depending on language) of integers and, assuming that the array is ordered according to an _in-order_ traversal of a complete binary tree, returns an array that contains the values of the tree in breadth-first order.

__Example 1:__
Let the input array be `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]`. This array contains the values of the following complete binary tree. 

```
          _ 7_
        /      \
       4        9
     /   \     / \
   2      6   8   10
  / \     /
 1   3   5
```
In this example, the input array happens to be sorted, but that is _not_ a requirement.

__Output 1:__ The output of the function shall be an array containing the values of the nodes of the binary tree read top-to-bottom, left-to-right. In this example, the returned array should be:

```[7, 4, 9, 2, 6, 8, 10, 1, 3, 5]```

__Example 2:__
Let the input array be `[1, 2, 2, 6, 7, 5]`. This array contains the values of the following complete binary tree. 

```
        6
      /   \
    2       5
   / \     /
  1   2   7

```
Note that an in-order traversal of this tree produces the input array.

__Output 2:__ The output of the function shall be an array containing the values of the nodes of the binary tree read top-to-bottom, left-to-right. In this example, the returned array should be:

```[6, 2, 5, 1, 2, 7]```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded