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
/* helper modified by LLM (iteration 2): added decreases clause to prove loop termination */
fn create_vec_with_len(len: usize) -> (result: Vec<i32>)
    ensures result.len() == len,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
        decreases len - i
    {
        result.push(0);
        i = i + 1;
    }
    result
}
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
    /* code modified by LLM (iteration 2): No logical changes were needed, just fixing a helper. */
    if count > 0 {
        create_vec_with_len(count as usize)
    } else {
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}