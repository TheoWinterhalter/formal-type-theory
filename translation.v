Require Import reflections.

Module Dummy : Param.
End Dummy.

Module Source := Theory (Dummy).
Module Target := Theory (Dummy).

Fail Check Source = Target.
