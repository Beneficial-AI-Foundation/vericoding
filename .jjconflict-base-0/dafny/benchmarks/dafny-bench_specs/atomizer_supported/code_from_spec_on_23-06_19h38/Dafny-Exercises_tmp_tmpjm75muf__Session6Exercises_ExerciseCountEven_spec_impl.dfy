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


/* code modified by LLM (iteration 4): Added helper function for forward counting */
function CountEvenForward(s: seq<int>, start: nat): int
    requires positive(s)
    requires start <= |s|
{
    if start == |s| then 0
    else (if s[start] % 2 == 0 then 1 else 0) + CountEvenForward(s, start + 1)
}

/* code modified by LLM (iteration 4): Added lemma to prove equivalence between forward and backward counting */
lemma CountEvenForwardCorrect(s: seq<int>, start: nat)
    requires positive(s)
    requires start <= |s|
    ensures CountEvenForward(s, start) == CountEven(s[start..])
{
    if start == |s| {
        assert s[start..] == [];
    } else {
        assert s[start..] == [s[start]] + s[start+1..];
        CountEvenForwardCorrect(s, start + 1);
    }
}

/* code modified by LLM (iteration 4): Added helper lemma to establish equivalence between forward and backward counting */
lemma CountEvenEquivalence(s: seq<int>)
    requires positive(s)
    ensures CountEven(s) == CountEvenForward(s, 0)
{
    CountEvenForwardCorrect(s, 0);
}

// IMPL 

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{
    /* code modified by LLM (iteration 4): Establish equivalence at the start */
    CountEvenEquivalence(v[..]);
    
    n := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Updated loop with corrected invariant */
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant n == CountEvenForward(v[..], 0) - CountEvenForward(v[..], i)
    {
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Final assertion to connect back to original CountEven */
    assert i == v.Length;
    assert CountEvenForward(v[..], i) == 0;
    assert n == CountEvenForward(v[..], 0);
    assert CountEven(v[..]) == CountEvenForward(v[..], 0);
}