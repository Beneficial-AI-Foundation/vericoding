// <vc-preamble>
use vstd::prelude::*;

verus! {

struct FileHandle {

    path: String,

    is_binary: bool,

    position: nat,
}

enum DType {

    Float32,

    Float64,

    Int32,

    Int64,

    UInt8,
}

spec fn dtype_size_bytes(dtype: DType) -> nat {
    match dtype {
        DType::Float32 => 4,
        DType::Float64 => 8,
        DType::Int32 => 4,
        DType::Int64 => 8,
        DType::UInt8 => 1,
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn max_nat(a: nat, b: nat) -> nat { if a >= b { a } else { b } }

fn default_i32() -> i32 { 0 }

proof fn lemma_mul_nat_nonneg(a: nat, b: nat) ensures a * b >= 0 { }
// </vc-helpers>

// <vc-spec>
fn fromfile(file: FileHandle, dtype: DType, count: i32, sep: &str, offset: nat) -> (result: Vec<i32>)
    requires
        count == -1 || count > 0,
        sep == "" ==> file.is_binary == true,
        file.is_binary == true ==> sep == "",
    ensures
        count > 0 ==> result.len() == count as usize,

        file.is_binary == true ==> (
            #[trigger] (result.len() * dtype_size_bytes(dtype))
            >= 0
        ),

        true,

        true,
// </vc-spec>
// <vc-code>
{
    let target_len: usize = if count > 0 { count as usize } else { 0usize };
    let mut v: Vec<i32> = Vec::new();
    while v.len() < target_len
        invariant
            v.len() <= target_len,
        decreases target_len - v.len()
    {
        v.push(0);
    }
    v
}
// </vc-code>

}
fn main() {}