#!/bin/sh
# Print interfaces of a .v file,
# i.e. all but Proof..Qed or Proof..Defined
grep -v 'Proof.*Qed' $* | sed -e '/Proof/,/\(Qed\|Defined\)/d'
