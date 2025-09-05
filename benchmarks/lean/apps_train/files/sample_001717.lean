Your task is to build a model^(1) which can predict y-coordinate.
You can pass tests if predicted y-coordinates are inside error margin.

You will receive train set which should be used to build a model. 
After you build a model tests will call function ```predict``` and pass x to it. 

Error is going to be calculated with RMSE.

Side note: Points in test cases are from different polynomials (up to 5th degree).

Easier version: Data mining #1

Blocked libraries: sklearn, pandas, tensorflow, numpy, scipy

Explanation
[1] A mining model is created by applying an algorithm to data, but it is more than an algorithm or a metadata container: it is a set of data, statistics, and patterns that can be applied to new data to generate predictions and make inferences about relationships.

def Point := Float × Float 

structure Datamining where
  points : List Point

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded