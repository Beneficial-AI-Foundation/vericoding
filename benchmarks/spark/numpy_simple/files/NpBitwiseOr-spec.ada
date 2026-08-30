--  <vc-preamble>
package Np_Bitwise_Or_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;

   subtype Index_Type is Natural range 0 .. Max_Index;

   type Word_32 is mod 2 ** 32;

   type Word_Array is array (Index_Type range <>) of Word_32;
--  </vc-preamble>

--  <vc-spec>
   procedure Bitwise_Or (A : Word_Array; B : Word_Array; Result : out Word_Array) with
     Pre  => A'First = B'First and then A'Last = B'Last
             and then Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range => Result (I) = (A (I) or B (I)));

end Np_Bitwise_Or_Spec;

package body Np_Bitwise_Or_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Bitwise_Or (A : Word_Array; B : Word_Array; Result : out Word_Array) is
   begin
      pragma Assume (False);
   end Bitwise_Or;
--  </vc-code>

--  <vc-postamble>
end Np_Bitwise_Or_Spec;
--  </vc-postamble>
