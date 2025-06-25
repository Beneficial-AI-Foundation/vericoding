use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum Abc {
    End,
    Wrapper(Seq<Abc>),
}

pub proof fn seq_rank0(a: Abc)
    ensures
        a != Abc::Wrapper(seq![a]),
{
}

pub proof fn seq_rank1(s: Seq<Abc>)
    requires
        s != seq![],
    ensures
        s[0] != Abc::Wrapper(s),
{
}

#[derive(PartialEq, Eq, Structural)]
pub enum Def {
    End,
    MultiWrapper(Multiset<Def>),
}

pub proof fn multiset_rank(a: Def)
    ensures
        a != Def::MultiWrapper(multiset!{a}),
{
}

#[derive(PartialEq, Eq, Structural)]
pub enum Ghi {
    End,
    SetWrapper(Set<Ghi>),
}

pub proof fn set_rank(a: Ghi)
    ensures
        a != Ghi::SetWrapper(set!{a}),
{
}

}