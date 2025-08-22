
// ATOM 

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


// ATOM 

predicate isEven(i:int)
requires i>=0
{i%2==0}


// ATOM 

function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }


// ATOM 

lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
    ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
    ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  {}


// SPEC 

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{
}








