--  Use *.asu file extension for a subunit so that it is not included as a
--  a top level unit to be analysed using by the regression test system.
--  The gnat front-end will automatically analyse the subunit when it
--  encounters the sybprogram_body_stub.
pragma Source_File_Name (
			 Subunit_File_Name  => "*.asu",
			Dot_Replacement => "-");

procedure P (X : in out integer) is
   procedure Inc (N : in out Integer) is separate;
   Old_X : constant Integer := X;
begin
   --  The following assertion will fail because the value of Old_X is
   --  non-det.
   pragma Assert (X < Integer'Last);
   Inc (X);
   --  The following assert should succeed.
   pragma Assert (X = Old_X + 1);
end P;
