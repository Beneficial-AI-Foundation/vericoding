--  <vc-preamble>
package Np_Cum_Sum_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   subtype Total_Type is Integer range
     -((Max_Index + 1) * Max_Value) .. (Max_Index + 1) * Max_Value;
   type Total_Array is array (Index_Type range <>) of Total_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Cum_Sum (A : Int_Array; Result : out Total_Array) with
     Pre  => A'Length > 0
             and then Result'First = A'First and then Result'Last = A'Last,
     Post => Result (A'First) = A (A'First)
             and then (for all I in A'Range =>
                         (if I > A'First then Result (I) = Result (I - 1) + A (I)));

end Np_Cum_Sum_Spec;

package body Np_Cum_Sum_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
   procedure Cum_Sum (A : Int_Array; Result : out Total_Array) is
   begin
      Result := (others => 0);
      Result (A'First) := A (A'First);
      for I in A'First + 1 .. A'Last loop
         pragma Loop_Invariant (Result (A'First) = A (A'First));
         pragma Loop_Invariant
           (for all J in A'First .. I - 1 =>
              (if J > A'First then Result (J) = Result (J - 1) + A (J)));
         pragma Loop_Invariant
           (for all J in A'First .. I - 1 =>
              abs Result (J) <= (J - A'First + 1) * Max_Value);
         Result (I) := Result (I - 1) + A (I);
      end loop;
   end Cum_Sum;
--  </vc-code>

--  <vc-postamble>
end Np_Cum_Sum_Spec;
--  </vc-postamble>
