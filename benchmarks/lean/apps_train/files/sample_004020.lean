# Task
 You're standing at the top left corner of an `n × m` grid and facing towards the `right`. 

 Then you start walking one square at a time in the direction you are facing. 

 If you reach the border of the grid or if the next square you are about to visit has already been visited, you turn right. 

 You stop when all the squares in the grid are visited. What direction will you be facing when you stop?

 You can see the example of your long walk in the image below. The numbers denote the order in which you visit the cells.

 ![](https://i.gyazo.com/2fc5884d2c227a0ddeca503e6a0261be.png)

 Given two integers n and m, denoting the number of rows and columns respectively, find out the direction you will be facing at the end. 

 Output `"L"` for left, `"R"` for right, `"U"` for up, and `"D"` for down.

# Example:

 For `n = 3, m = 3`, the output should be `"R"`.

 This example refers to the picture given in the description. At the end of your walk you will be standing in the middle of the grid facing right.

# Input/Output

 - `[input]` integer `n`

 number of rows.

 `1 <= n <= 1000`

 - `[input]` integer `m`

 number of columns.

 `1 <= m <= 1000`

 - `[output]` a string

 The final direction.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
