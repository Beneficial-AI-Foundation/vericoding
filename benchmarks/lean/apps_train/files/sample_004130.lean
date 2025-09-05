## Euler's Method

We want to calculate the shape of an unknown curve which starts at a given point 
with a given slope. This curve satisfies an ordinary differential equation (ODE):

```math
\frac{dy}{dx} = f(x, y);\\
y(x_0) = y_0
```

The starting point `$ A_0 (x_0, y_0) $` is known as well as the slope to the curve 
at `$ A_0 $` and then the tangent line at `$ A_0 $` .

Take a small step along that tangent line up to a point `$ A_1 $`. Along this small step, 
the slope does not change too much, so `$ A_1 $` will be close to the curve. 
If we suppose that `$ A_1 $` is close enough to the curve, the same reasoning 
as for the point `$ A_1 $` above can be used for other points. 
After several steps, a polygonal curve `$ A_0, A_1, ..., A_n $` is computed. 
The error between the two curves will be small if the step is small.

We define points `$ A_0, A_1, A_2, ..., A_n $`
whose x-coordinates are `$ x_0, x_1, ..., x_n $`
and y-coordinates are such that `$ y_{k+1} = y_k + f(x_k, y_k) \times h $` 
where `$ h $` is the common step. If `$ T $` is the length `$ x_n - x_0 $` we have `$ h = T/n $`.

## Task

For this kata we will focus on the following differential equation:

```math
\frac{dy}{dx} = 2 - e^{-4x} - 2y; \\
A_0 = (0,1)
```
with `$ x ∈ [0, 1] $`. We will then take a uniform partition of the region of `$ x $` between `$ 0 $` and `$ 1 $` and split it into `$ n $` + 1 sections. `$ n $` will be the input to the function `ex_euler(n)` and since `$ T $` is always 1, `$ h = 1/n $`.

We know that an exact solution is
```math
y = 1 + 0.5e^{-4x} - 0.5e^{-2x}.
```
For each `$ x_k $` we are able to calculate the `$ y_k $` as well as the values `$ z_k $` of the exact solution.

Our task is, for a given number `$ n $` of steps, to return the mean (*truncated* to 6 decimal places)
of the relative errors between the `$ y_k $` (our aproximation) and the `$ z_k $` (the exact solution). 
For that we can use:

error in `$ A_k = abs(y_k - z_k) / z_k $` and then the mean is sum(errors in `$ A_k $`)/ (`$ n $` + 1)

## Examples

```python
ex_euler(10) should return: 0.026314 (truncated from 0.026314433214799246)
with
Y = [1.0,0.9..., 0.85..., 0.83..., 0.83..., 0.85..., 0.86..., 0.88..., 0.90..., 0.91..., 0.93...]
Z = [1.0, 0.9..., 0.88..., 0.87..., 0.87..., 0.88..., 0.89..., 0.90..., 0.91..., 0.93..., 0.94...]
Relative errors = [0.0, 0.02..., 0.04..., 0.04..., 0.04..., 0.03..., 0.03..., 0.02..., 0.01..., 0.01..., 0.01...]
```
`ex_euler(17)` should return: `0.015193 (truncated from 0.015193336263370796)`.
As expected, as `$ n $` increases, our error reduces.
### Links and graphs

Wiki article

![alternative text](http://i.imgur.com/vjK7edl.png)

Below comparison between approximation (red curve) and exact solution(blue curve) for n=100:
![alternative text](http://i.imgur.com/KufSkYEm.png)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded