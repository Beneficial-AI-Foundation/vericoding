//ATOM

datatype Steps = One | Two


// SPEC

method climbStairs(n: nat) returns (count: nat) 
  ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
}