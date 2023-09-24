/isotope id/s/>$//
/isotope id/s/^[ \t]*<//
/isotope id/s/=/ /g
/isotope id/s/"//g
/isotope id/s/^isotope id [^ ]* //p
/bo:exactMass/s/<\/scalar>$//
/bo:exactMass/s/^.*>/exactMass /p
/bo:relativeAbundance/s/<\/scalar>$//
/bo:relativeAbundance/s/^.*>/relativeAbundance /p
