In this kata, we will check is an array is (hyper)rectangular.  
A rectangular array is an N-dimensional array with fixed sized within one dimension. Its sizes can be repsented like A1xA2xA3...xAN. That means a N-dimensional array has N sizes. The 'As' are the hyperrectangular properties of an array.

You should implement a functions that returns a N-tuple with the arrays hyperrectangular properties or None if the array is not hyperrectangular.
```
hyperrectangularity_properties(arr)
```
## Note
An empty array IS rectagular and has one dimension of length 0
```
hyperrectangularity_properties([]) == (0,)
```
## Example
```
1D array
hyperrectangularity_properties([1,2,3]) == (3,)

2D arrays  

hyperrectangularity_properties(
                                [[0,1,2],
                                 [3,4,5],           
                                 [6,7,8]] ) == (3,3)                              
hyperrectangularity_properties(
                                [[0,1,2],
                                 [3,4,5]] ) == (2,3)
hyperrectangularity_properties( 
                                [[0,1,2],
                                 [3,4]  ] ) == None
3D arrays  
hyperrectangularity_properties(  
                                [
                                 [ [0], [2] ],
                                 [ [0], [2] ],  
                                 [ [0], [2] ]
                                              ] ) == (3,2,1)    
hyperrectangularity_properties(  
                                [
                                   [[0],[2]],
                                   [[0],[2,2]],   
                                   [[0],[2]]
                                              ] )  ==  None 
hyperrectangularity_properties(
                                [[ [], [], [] ]]
                                                ) ==  (1,3,0) 
```
### Heterogeneous Arrays can appear too
```
hyperrectangularity_properties(      
                                [[0,1,2],
                                 3,   
                                 [[4],5,6]] ) ==  None
hyperrectangularity_properties(      
                                [1,
                                 [1,2],   
                                 [[3],[4,[5]],[6]]
                                                  ] ) ==  None
                                                  hyperrectangularity_properties(
                                [[ [], [] ], [] ]
                                                  ) ==  None
hyperrectangularity_properties(
                                [ 1, [], [2, [3]] ]
                                                  ) ==  None
```
The first property shows the length of the outer layer. The second of the layer one step deeper and so on. The function should handle higher dimensions too.

## Input
##### N-dimensional array of integers

## Expected Ouput
##### An N-tuple with the hyperrectangularity properties

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
