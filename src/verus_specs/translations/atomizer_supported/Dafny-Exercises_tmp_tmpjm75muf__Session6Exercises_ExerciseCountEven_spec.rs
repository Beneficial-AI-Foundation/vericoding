// ATOM 

spec fn positive(s: Seq<int>) -> bool
{
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// ATOM 

spec fn isEven(i: int) -> bool
    requires i >= 0
{
    i % 2 == 0
}

// ATOM 

spec fn CountEven(s: Seq<int>) -> int
    requires positive(s)
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { (if s[s.len()-1] % 2 == 0 { 1 } else { 0 }) + CountEven(s.subrange(0, s.len()-1)) }
}

// ATOM 

proof fn ArrayFacts<T>()
    ensures forall|v: &Vec<T>| v.view().subrange(0, v.len() as int) == v.view(),
    ensures forall|v: &Vec<T>| v.view().subrange(0, v.len() as int) == v.view(),
    ensures forall|v: &Vec<T>| v.view().subrange(0, v.len() as int) == v.view(),
    ensures forall|v: &Vec<T>| v.view().subrange(0, v.len() as int).len() == v.len(),
    ensures forall|v: &Vec<T>| v.len() >= 1 ==> v.view().subrange(1, v.len() as int).len() == v.len() - 1,
    ensures forall|v: &Vec<T>| forall|k: nat| k < v.len() ==> v.view().subrange(0, k as int + 1).subrange(0, k as int) == v.view().subrange(0, k as int)
{
}

// SPEC 

pub fn mcountEven(v: &Vec<int>) -> (n: int)
    requires positive(v.view())
    ensures n == CountEven(v.view())
{
}