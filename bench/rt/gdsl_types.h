/*
 * This file is part of the Generic Data Structures Library (GDSL).
 * Copyright (C) 1998-2006 Nicolas Darnis <ndarnis@free.fr>.
 *
 * The GDSL library is free software; you can redistribute it and/or 
 * modify it under the terms of the GNU General Public License as 
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * The GDSL library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with the GDSL library; see the file COPYING.
 * If not, write to the Free Software Foundation, Inc., 
 * 59 Temple Place, Suite 330, Boston, MA  02111-1307, USA.
 *
 * $RCSfile: gdsl_types.h,v $
 * $Revision: 1.25 $
 * $Date: 2012/08/21 13:00:04 $
 */


#ifndef _GDSL_TYPES_H_
#define _GDSL_TYPES_H_

#ifndef MEMCAD_INRIA
#include <stdio.h>
#endif /* MEMCAD_INRIA */

#ifdef __cplusplus
extern "C" 
{
#endif /* __cplusplus */


/**
 * @defgroup gdsl_types GDSL types
 * @{
 */


/**
 * @brief GDSL Constants.
 */
typedef enum
{
    /** Memory allocation error */
    GDSL_ERR_MEM_ALLOC = -1,

    /** For stopping a parsing function */
    GDSL_MAP_STOP = 0,

    /** For continuing a parsing function */
    GDSL_MAP_CONT = 1,

    /** To indicate an inserted value */
    GDSL_INSERTED,

    /** To indicate a founded value */
    GDSL_FOUND

} gdsl_constant_t;

/**
 */
typedef enum
{
    /** Element position undefined */
    GDSL_LOCATION_UNDEF     = 0,

    /** Element is at head position */
    /* (for _node, _list, list, queue) */
    GDSL_LOCATION_HEAD      = 1,

    /** Element is on leaf position */
    /* (for _bintree, _bstree) */
    GDSL_LOCATION_ROOT      = 1,

    /** Element is at top position */
    /* (for stack)                 */
    GDSL_LOCATION_TOP       = 1,

    /** Element is at tail position */
    /* (for _node, _list, list, queue) */
    GDSL_LOCATION_TAIL      = 2,
   
    /** Element is on root position */
    /* (for _bintree, _bstree) */
    GDSL_LOCATION_LEAF      = 2,

    /** Element is at bottom position */
    /*  (for stack) */
    GDSL_LOCATION_BOTTOM    = 2,

    /** Element is the first */
    /* (for perm) */
    GDSL_LOCATION_FIRST     = 1,

    /** Element is the last */
    /* (for perm) */
    GDSL_LOCATION_LAST      = 2,

    /** Element is on first column */
    /* (for 2darray) */
    GDSL_LOCATION_FIRST_COL = 1,

    /** Element is on last column */
    /* (for 2darray) */
    GDSL_LOCATION_LAST_COL  = 2,

    /** Element is on first row */
    /* (for 2darray) */
    GDSL_LOCATION_FIRST_ROW = 4,

    /** Element is on last row */
    /* (for 2darray) */
    GDSL_LOCATION_LAST_ROW  = 8

} gdsl_location_t;

/**
 * @brief GDSL element type.
 *
 * All GDSL internal data structures contains a field of this type. This field 
 * is for GDSL users to store their data into GDSL data structures.
 */
// commented out for memcad
/* typedef int* gdsl_element_t; */

/**
 * @brief GDSL Alloc element function type.
 *
 * This function type is for allocating a new gdsl_element_t variable.
 * The USER_DATA argument should be used to fill-in the new element.
 *
 * @param USER_DATA user data used to create the new element.
 * @return the newly allocated element in case of success.
 * @return NULL in case of failure.
 * @see gdsl_free_func_t
 */
// commented out for memcad
/* typedef gdsl_element_t  */
/* (* gdsl_alloc_func_t) (void* USER_DATA); */

/**
 * @brief GDSL Free element function type.
 *
 * This function type is for freeing a gdsl_element_t variable.
 * The element must have been previously allocated by a function of 
 * gdsl_alloc_func_t type.
 * A free function according to gdsl_free_func_t must free the ressources 
 * allocated by the corresponding call to the function of type 
 * gdsl_alloc_func_t. The GDSL functions doesn't check if E != NULL before 
 * calling this function.
 *
 * @param E The element to deallocate.
 * @see gdsl_alloc_func_t
 */
// commented out for memcad
/* typedef void  */
/* (* gdsl_free_func_t) (gdsl_element_t E); */

/**
 * @brief GDSL Copy element function type.
 *
 * This function type is for copying gdsl_element_t variables.
 *
 * @param E The gdsl_element_t variable to copy.
 * @return the copied element in case of success.
 * @return NULL in case of failure.
 */
// commented out for memcad
/* typedef gdsl_element_t  */
/* (* gdsl_copy_func_t) (const gdsl_element_t E); */

/**
 * @brief GDSL Map element function type.
 *
 * This function type is for mapping a gdsl_element_t variable from a GDSL
 * data structure.
 * The optional USER_DATA could be used to do special thing if needed.
 *
 * @param E The actually mapped gdsl_element_t variable.
 * @param LOCATION The location of E in the data structure.
 * @param USER_DATA User's datas.
 * @return GDSL_MAP_STOP if the mapping must be stopped.
 * @return GDSL_MAP_CONT if the mapping must be continued.
 */
// commented out for memcad
/* typedef int  */
/* (* gdsl_map_func_t) (const gdsl_element_t E, */
/* 		     gdsl_location_t LOCATION, */
/* 		     void* USER_DATA); */

/**
 * @brief GDSL Comparison element function type.
 *
 * This function type is used to compare a gdsl_element_t variable with a user
 * value.
 * The E argument is always the one in the GDSL data structure, VALUE is always 
 * the one the user wants to compare E with.
 *
 * @param E The gdsl_element_t variable contained into the data structure to
 * compare from.
 * @param VALUE The user data to compare E with.
 * @return < 0  if E is assumed to be less than VALUE.
 * @return 0 if E is assumed to be equal to VALUE.
 * @return > 0 if E is assumed to be greather than VALUE.
 */
// commented out for memcad
/* typedef long int */
/* (* gdsl_compare_func_t) (const gdsl_element_t E, */
/* 			 void* VALUE */
/* 			 ); */

/**
 * @brief GDSL Write element function type.
 *
 * This function type is for writing a gdsl_element_t E to OUTPUT_FILE. 
 * Additional USER_DATA could be passed to it.
 *
 * @param E The gdsl element to write.
 * @param OUTPUT_FILE The file where to write E.
 * @param LOCATION The location of E in the data structure.
 * @param USER_DATA User's datas.
 */
// commented out for memcad
/* typedef void  */
/* (* gdsl_write_func_t) (const gdsl_element_t E, */
/* 		       FILE* OUTPUT_FILE, */
/* 		       gdsl_location_t LOCATION, */
/* 		       void* USER_DATA); */


#ifndef WITHOUT_GDSL_TYPES

#ifndef MEMCAD_INRIA
#include <sys/types.h>
#endif /* MEMCAD_INRIA */

#ifndef HAVE_ULONG
typedef unsigned long int ulong;
#endif /* HAVE_ULONG */

#ifndef HAVE_USHORT
typedef unsigned short int ushort;
#endif /* HAVE_USHORT */

#ifndef __cplusplus

#ifdef TRUE
#undef TRUE
#endif

#ifdef FALSE
#undef FALSE
#endif

#ifdef bool
#undef bool
#endif

/**
 * GDSL boolean type.
 * Defines _NO_LIBGDSL_TYPES_ at compilation time if you don't want them.
 */
typedef enum 
{
  /** FALSE boolean value */
  FALSE = 0,

  /** TRUE boolean value */
  TRUE = 1 
} bool;

#endif /* not __cplusplus */

#endif /* not WITHOUT_GDSL_TYPES */


/*
 * @}
 */


#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* _GDSL_TYPES_H_ */


/** EMACS **
 * Local variables:
 * mode: c
 * c-basic-offset: 4
 * End:
 */
