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
 * $RCSfile: gdsl_heap.h,v $
 * $Revision: 1.11 $
 * $Date: 2006/03/07 16:32:58 $
 */


#ifndef _GDSL_HEAP_H_
#define _GDSL_HEAP_H_

#ifndef MEMCAD_INRIA
#include <stdio.h>
#endif /* MEMCAD_INRIA */

#include "gdsl_types.h"


#ifdef __cplusplus
extern "C" 
{
#endif /* __cplusplus */


/**
 * @defgroup gdsl_heap Heap manipulation module
 * @{
 */


/**
 * @brief GDSL heap type.
 *
 * This type is voluntary opaque. Variables of this kind could'nt be directly
 * used, but by the functions of this module.
 */
typedef heap* gdsl_heap_t;

/******************************************************************************/
/* Management functions of heaps                                              */
/******************************************************************************/

/**
 * @brief Create a new heap.
 *
 * Allocate a new heap data structure which name is set to a copy of NAME.
 * The function pointers ALLOC_F, FREE_F and COMP_F could be used to 
 * respectively, alloc, free and compares elements in the heap. These pointers 
 * could be set to NULL to use the default ones:
 * - the default ALLOC_F simply returns its argument
 * - the default FREE_F does nothing
 * - the default COMP_F always returns 0
 *
 * @note Complexity: O( 1 )
 * @pre nothing
 * @param NAME The name of the new heap to create
 * @param ALLOC_F Function to alloc element when inserting it in the heap
 * @param FREE_F Function to free element when removing it from the heap
 * @param COMP_F Function to compare elements into the heap
 * @return the newly allocated heap in case of success.
 * @return NULL in case of insufficient memory.
 * @see gdsl_heap_free()
 * @see gdsl_heap_flush()
 */
extern gdsl_heap_t
gdsl_heap_alloc ();

/**
 * @brief Destroy a heap.
 * 
 * Deallocate all the elements of the heap H by calling H's FREE_F function
 * passed to gdsl_heap_alloc(). The name of H is deallocated and H is 
 * deallocated itself too.
 *
 * @note Complexity: O( |H| )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to destroy
 * @see gdsl_heap_alloc()
 * @see gdsl_heap_flush()
 */
extern void
gdsl_heap_free (gdsl_heap_t H);

/**
 * @brief Flush a heap.
 *
 * Deallocate all the elements of the heap H by calling H's FREE_F function
 * passed to gdsl_heap_alloc(). H is not deallocated itself and H's name is not
 * modified.
 *
 * @note Complexity: O( |H| )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to flush
 * @see gdsl_heap_alloc()
 * @see gdsl_heap_free()
 */
extern void
gdsl_heap_flush (gdsl_heap_t H);

/******************************************************************************/
/* Consultation functions of heaps                                            */
/******************************************************************************/

/**
 * @brief Get the size of a heap.
 * @note Complexity: O( 1 )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to get the size from
 * @return the number of elements of H (noted |H|).
 */
extern ulong
gdsl_heap_get_size (const gdsl_heap_t H);

/**
 * @brief Get the top of a heap.
 * @note Complexity: O( 1 )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to get the top from
 * @return the element contained at the top position of the heap H if H is not
 * empty. The returned element is not removed from H.
 * @return NULL if the heap H is empty.
 * @see gdsl_heap_set_top()
 */
extern gdsl_element_t
gdsl_heap_get_top (const gdsl_heap_t H);

/**
 * @brief Check if a heap is empty.
 * @note Complexity: O( 1 )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to check
 * @return TRUE if the heap H is empty.
 * @return FALSE if the heap H is not empty.
 */
extern bool 
gdsl_heap_is_empty (const gdsl_heap_t H);

/******************************************************************************/
/* Modification functions of heaps                                            */
/******************************************************************************/
  

/**
 * @brief Substitute the top element of a heap by a lesser one.
 *
 * Try to replace the top element of a heap by a lesser one.
 *
 * @note Complexity: O( log ( |H| ) )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to substitute the top element
 * @param VALUE the value to substitute to the top
 * @return The old top element value in case VALUE is lesser than all other H 
 * elements.
 * @return NULL in case of VALUE is greather or equal to all other H elements.
 * @see gdsl_heap_get_top()
 */
extern gdsl_element_t
gdsl_heap_set_top (gdsl_heap_t H, 
		   int* VALUE);

/**
 * @brief Insert an element into a heap (PUSH).
 * 
 * Allocate a new element E by calling H's ALLOC_F function on VALUE.
 * The element E is then inserted into H at the good position to ensure H is
 * always a heap.
 *
 * @note Complexity: O( log ( |H| ) )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to modify
 * @param VALUE The value used to make the new element to insert into H
 * @return the inserted element E in case of success.
 * @return NULL in case of insufficient memory.
 * @see gdsl_heap_alloc()
 * @see gdsl_heap_remove()
 * @see gdsl_heap_delete()
 * @see gdsl_heap_get_size()
 */
extern gdsl_element_t
gdsl_heap_insert (gdsl_heap_t H,
		  int* VALUE);

/**
 * @brief Remove the top element from a heap (POP).
 *
 * Remove the top element from the heap H. The element is removed from H and
 * is also returned.
 *
 * @note Complexity: O( log ( |H| ) )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to modify
 * @return the removed top element.
 * @return NULL if the heap is empty.
 * @see gdsl_heap_insert()
 * @see gdsl_heap_delete_top()
 */
extern gdsl_element_t
gdsl_heap_remove_top (gdsl_heap_t H);

/**
 * @brief Delete the top element from a heap.
 *
 * Remove the top element from the heap H. The element is removed from H and
 * is also deallocated using H's FREE_F function passed to gdsl_heap_alloc(),
 * then H is returned.
 *
 * @note Complexity: O( log ( |H| ) )
 * @pre H must be a valid gdsl_heap_t
 * @param H The heap to modify
 * @return the modified heap after removal of top element.
 * @return NULL if heap is empty.
 * @see gdsl_heap_insert()
 * @see gdsl_heap_remove_top()
 */
extern gdsl_heap_t
gdsl_heap_delete_top (gdsl_heap_t H);

/******************************************************************************/
/* Parse functions of heaps                                                   */
/******************************************************************************/

/**
 * @brief Parse a heap.
 *
 * Parse all elements of the heap H. The MAP_F function is called on each 
 * H's element with USER_DATA argument. If MAP_F returns GDSL_MAP_STOP then
 * gdsl_heap_map() stops and returns its last examinated element.
 *
 * @note Complexity: O( |H| )
 * @pre H must be a valid gdsl_heap_t & MAP_F != NULL
 * @param H The heap to map
 * @param MAP_F The map function.
 * @param USER_DATA User's datas passed to MAP_F
 * @return the first element for which MAP_F returns GDSL_MAP_STOP.
 * @return NULL when the parsing is done.
 */
extern gdsl_element_t
gdsl_heap_map_forward (const gdsl_heap_t H,
		       void* USER_DATA);

/******************************************************************************/
/* Input/output functions of heaps                                            */
/******************************************************************************/

/**
 * @brief Write all the elements of a heap to a file.
 *
 * Write the elements of the heap H to OUTPUT_FILE, using WRITE_F function.
 * Additionnal USER_DATA argument could be passed to WRITE_F.
 *
 * @note Complexity: O( |H| )
 * @pre H must be a valid gdsl_heap_t & OUTPUT_FILE != NULL & WRITE_F != NULL
 * @param H The heap to write.
 * @param WRITE_F The write function.
 * @param OUTPUT_FILE The file where to write H's elements.
 * @param USER_DATA User's datas passed to WRITE_F.
 * @see gdsl_heap_write_xml()
 * @see gdsl_heap_dump()
 */
extern void
gdsl_heap_write (const gdsl_heap_t H,
		 FILE* OUTPUT_FILE,
		 void* USER_DATA);

/**
 * @brief Dump the internal structure of a heap to a file.
 *
 * Dump the structure of the heap H to OUTPUT_FILE. If WRITE_F != NULL,
 * then uses WRITE_F to write H's elements to OUTPUT_FILE.
 * Additionnal USER_DATA argument could be passed to WRITE_F.
 *
 * @note Complexity: O( |H| )
 * @pre H must be a valid gdsl_heap_t & OUTPUT_FILE != NULL
 * @param H The heap to write
 * @param WRITE_F The write function
 * @param OUTPUT_FILE The file where to write H's elements
 * @param USER_DATA User's datas passed to WRITE_F
 * @see gdsl_heap_write()
 * @see gdsl_heap_write_xml()
 */
extern void
gdsl_heap_dump (const gdsl_heap_t H,
		FILE* OUTPUT_FILE,
		void* USER_DATA);

/*
 * @}
 */


#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* _GDSL_HEAP_H_ */


/** EMACS **
 * Local variables:
 * mode: c
 * c-basic-offset: 4
 * End:
 */

