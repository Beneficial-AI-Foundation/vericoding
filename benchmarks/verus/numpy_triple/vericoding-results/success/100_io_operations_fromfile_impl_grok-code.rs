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
/* helper modified by LLM (iteration 4): added ensures clause to specify the length of the returned vector */
fn create_vec_of_len(len: usize) -> (result: Vec<i8>)
    ensures result.len() == len as nat
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i as nat,
            i <= len,
        decreases len - i
    {
        v.push(0i8);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn fromfile(file: FileHandle, dtype: DType, count: i8, sep: &str, offset: u8) -> (result: Vec<i8>)
    requires
        count == -1 || count > 0,
        sep == "" ==> file.is_binary == true,
        file.is_binary == true ==> sep == "",
    ensures
        count > 0 ==> result.len() == count as int as usize,

        file.is_binary == true ==> (
            #[trigger] (result@.len() * dtype_size_bytes(dtype))
            >= 0
        ),

        true,

        true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): used len variable and added asserts to prove Cast equality */
    let result = if count > 0 {
        let len = count as usize;
        let r = create_vec_of_len(len);
        proof {
            assert(count as int as usize == len);
            assert(r.len() == len as nat);
        }
        r
    } else {
        Vec::new()
    };
    result
}
// </vc-code>

}
fn main() {}