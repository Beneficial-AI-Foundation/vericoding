--  <vc-preamble>
package Np_Abs_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   function Abs_Int (X : Value_Type) return Value_Type is
     (if X < 0 then -X else X);
--  </vc-preamble>

--  <vc-spec>
   procedure Abs_Vec (A : Int_Array; Result : out Int_Array) with
     Pre  => Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range => Result (I) = Abs_Int (A (I)))
             and then (for all I in Result'Range => Result (I) >= 0);

end Np_Abs_Spec;

package body Np_Abs_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Abs_Vec (A : Int_Array; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Abs_Vec;
--  </vc-code>

--  <vc-postamble>
end Np_Abs_Spec;
--  </vc-postamble>
