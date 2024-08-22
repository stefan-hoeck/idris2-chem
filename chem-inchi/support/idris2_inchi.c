// Copyright Stefan Höck

#include "inchi_api.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

int idris_gen_inchi(const char *mol, char *buffer, size_t buflen) {
  int result;
  inchi_Output iout, *piout = &iout;

  memset(piout, 0, sizeof( *piout ));
  result = MakeINCHIFromMolfileText(mol, "-WM5000", piout);

  if (strlen(iout.szInChI) < buflen) {
    strcpy(buffer, iout.szInChI);
  }

  FreeINCHI( piout );
  return result;
}
