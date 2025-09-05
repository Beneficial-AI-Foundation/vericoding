#### Background: 

A linear regression line has an equation in the form `$Y = a + bX$`, where `$X$` is the explanatory variable and `$Y$` is the dependent variable. The parameter `$b$` represents the *slope* of the line, while `$a$` is called the *intercept* (the value of `$y$` when `$x = 0$`).

For more details visit the related [wikipedia page](http://en.wikipedia.org/wiki/Simple_linear_regression).

---
---
#### Task:
The function that you have to write accepts two list/array, `$x$` and `$y$`,  representing the coordinates of the points to regress (so that, for example, the first point has coordinates (`x[0], y[0]`)).

Your function should return a tuple (in Python) or an array (any other language) of two elements: `a` (intercept) and `b` (slope) in this order.

You must round your result to the first 4 decimal digits

#### Formula:

`$x_i$` and `$y_i$` is `$x$` and `$y$` co-ordinate of `$i$`-th point;  
`$n$` is length of input.  

`$a =  \dfrac{\sum x_i^2\cdot \sum y_i - \sum x_i \cdot\sum x_iy_i}{n\sum x_i^2 - (\sum x_i)^2}$`

`$b =  \dfrac{n\sum x_i y_i - \sum x_i \cdot \sum y_i}{n\sum x^2_i - (\sum x_i)^2}$`
#### Examples:

```python
regressionLine([25,30,35,40,45,50], [78,70,65,58,48,42]) == (114.381, -1.4457)

regressionLine([56,42,72,36,63,47,55,49,38,42,68,60], [147,125,160,118,149,128,150,145,115,140,152,155]) == (80.7777, 1.138)
```
----

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
