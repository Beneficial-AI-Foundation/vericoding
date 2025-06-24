// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ATOM 
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Abc = End | Wrapper(seq<Abc>)
// ATOM 

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
                       // The reason we need the assert is to match the trigger in the rank axioms produced
                       // for datatypes containing sequences.
                       // See "is SeqType" case of AddDatatype in Translator.cs
}


// ATOM 

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
}


// ATOM 

datatype Def = End | MultiWrapper(multiset<Def>)
// ATOM 

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
}
)
{
}

// ATOM 

datatype Ghi = End | SetWrapper(set<Ghi>)
// ATOM 

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
}
)
{
}

)
{
}

