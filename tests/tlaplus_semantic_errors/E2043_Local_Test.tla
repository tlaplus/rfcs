One of the most basic errors there is: referring to an undefined symbol, or a
symbol that should not be visible.
---- MODULE E2043_Local_Test ----
---- MODULE Inner ----
LOCAL def == 0
====
INSTANCE Inner
op == def
====

