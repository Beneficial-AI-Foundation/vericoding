// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
// SPEC 
// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
pub fn MinOfMultiset(m: multiset<int>) -> (min: int)
    requires(m != multiset{})
    ensures(min in m)
    ensures(forall |z| z in m ==> min <= z)
{
}

// Ekki má breyta þessu falli.
// SPEC 

// Ekki má breyta þessu falli.
pub fn Test(m: multiset<int>)
{
}

//ATOM_PLACEHOLDER_Main

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
// SPEC 

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
pub fn Sort(m: multiset<int>) -> (s: seq<int>)
    // Setjið viðeigandi ensures klausur hér
    ensures(multiset(s) == m)
    ensures(forall |p,q| 0 <= p < q < |s| ==> s[p] <= s[q])
{
}