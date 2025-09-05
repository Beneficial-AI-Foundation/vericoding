Hi! Welcome to my first kata.

In this kata the task is to take a list of integers (positive and negative) and split them according to a simple rule; those ints greater than or equal to the key, and those ints less than the key (the itself key will always be positive).

However, in this kata the goal is to sort the numbers IN PLACE, so DON'T go messing around with the order in with the numbers appear.

You are to return a nested list. If the list is empty, simply return an empty list.

Confused? Okay, let me walk you through an example...

    The input is: [1, 1, 1, 0, 0, 6, 10, 5, 10], the key is: 6
Okay so the first five numbers are less than the key, 6, so we group them together.

    [1, 1, 1, 0, 0]
The next two numbers, 6 & 10, are both >= 6 to they belong in a seperate group, which we will add to the first group. Like so:

    [[1, 1, 1, 0, 0], [6, 10]]
The next two numbers are 5 & 10. Since the key is 6 these two numbers form seperate groups, which we will add to the previous result. like so:

    [[1, 1, 1, 0, 0], [6, 10], [5], [10]]
And voila! We're done.

Here are a few more basic examples:

    group_ints([1, 0], key= 0)  
    --> [[1,0]]

    group_ints([1, 0, -1, 5], key= 0) 
    --> [[1, 0], [-1], [5]]

    group_ints([1, 0, -1, 5], key= 5) 
    --> [[1, 0, -1], [5]]

Good luck guys/gals!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
