# Introduction

You are the developer working on a website which features a large counter on its homepage, proudly displaying the number of happy customers who have downloaded your companies software.

You have been tasked with adding an effect to this counter to make it more interesting.  

Instead of just displaying the count value immediatley when the page loads, we want to create the effect of each digit cycling through its preceding numbers before stopping on the actual value.

# Task

As a step towards achieving this; you have decided to create a function that will produce a multi-dimensional array out of the hit count value.  Each inner dimension of the array represents an individual digit in the hit count, and will include all numbers that come before it, going back to 0.

## Rules
* The function will take one argument which will be a four character `string` representing hit count
* The function must return a multi-dimensional array containing four inner arrays
* The final value in each inner array must be the actual value to be displayed
* Values returned in the array must be of the type `number`

**Examples**

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded