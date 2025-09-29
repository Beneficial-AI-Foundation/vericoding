// <vc-preamble>
use vstd::prelude::*;

verus! {

enum DataType {

    ScalarInt,

    ScalarFloat,

    ScalarComplex,

    ScalarBool,

    ScalarString,

    ArrayType,

    CompositeType,

    UnknownType,
}

spec fn is_scalar_type(dt: DataType) -> bool {
    match dt {
        DataType::ScalarInt => true,
        DataType::ScalarFloat => true,
        DataType::ScalarComplex => true,
        DataType::ScalarBool => true,
        DataType::ScalarString => true,
        DataType::ArrayType => false,
        DataType::CompositeType => false,
        DataType::UnknownType => false,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Lemma equating is_scalar_type with constructor disjunction */
proof fn lemma_is_scalar_type_equiv(dt: DataType)
    ensures
        is_scalar_type(dt) ==
        (dt == DataType::ScalarInt ||
         dt == DataType::ScalarFloat ||
         dt == DataType::ScalarComplex ||
         dt == DataType::ScalarBool ||
         dt == DataType::ScalarString),
{
    match dt {
        DataType::ScalarInt => { }
        DataType::ScalarFloat => { }
        DataType::ScalarComplex => { }
        DataType::ScalarBool => { }
        DataType::ScalarString => { }
        DataType::ArrayType => { }
        DataType::CompositeType => { }
        DataType::UnknownType => { }
    }
}
// </vc-helpers>

// <vc-spec>
fn issctype(rep: DataType) -> (result: bool)
    ensures result == (rep == DataType::ScalarInt || 
                      rep == DataType::ScalarFloat || 
                      rep == DataType::ScalarComplex || 
                      rep == DataType::ScalarBool || 
                      rep == DataType::ScalarString)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid runtime equality on DataType; use match and prove postcondition via lemma */
    let result = match rep {
        DataType::ScalarInt
        | DataType::ScalarFloat
        | DataType::ScalarComplex
        | DataType::ScalarBool
        | DataType::ScalarString => true,
        DataType::ArrayType
        | DataType::CompositeType
        | DataType::UnknownType => false,
    };
    proof {
        lemma_is_scalar_type_equiv(rep);
        match rep {
            DataType::ScalarInt => {
                assert(rep == DataType::ScalarInt);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::ScalarFloat => {
                assert(rep == DataType::ScalarFloat);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::ScalarComplex => {
                assert(rep == DataType::ScalarComplex);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::ScalarBool => {
                assert(rep == DataType::ScalarBool);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::ScalarString => {
                assert(rep == DataType::ScalarString);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::ArrayType => {
                assert(rep == DataType::ArrayType);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(!is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::CompositeType => {
                assert(rep == DataType::CompositeType);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(!is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
            DataType::UnknownType => {
                assert(rep == DataType::UnknownType);
                assert(is_scalar_type(rep) == (
                    rep == DataType::ScalarInt ||
                    rep == DataType::ScalarFloat ||
                    rep == DataType::ScalarComplex ||
                    rep == DataType::ScalarBool ||
                    rep == DataType::ScalarString
                ));
                assert(!is_scalar_type(rep));
                assert(result == is_scalar_type(rep));
            }
        }
        assert(result == (
            rep == DataType::ScalarInt ||
            rep == DataType::ScalarFloat ||
            rep == DataType::ScalarComplex ||
            rep == DataType::ScalarBool ||
            rep == DataType::ScalarString
        ));
    }
    result
}
// </vc-code>

}
fn main() {}