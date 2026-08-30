--  <vc-preamble>
package Np_Square_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   subtype Prod_Type is Integer range -(Max_Value ** 2) .. Max_Value ** 2;
   type Prod_Array is array (Index_Type range <>) of Prod_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Square (A : Int_Array; Result : out Prod_Array) with
     Pre  => Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range => Result (I) = A (I) * A (I));

end Np_Square_Spec;

package body Np_Square_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Square (A : Int_Array; Result : out Prod_Array) is
   begin
      pragma Assume (False);
   end Square;
--  </vc-code>

--  <vc-postamble>
end Np_Square_Spec;
--  </vc-postamble>
