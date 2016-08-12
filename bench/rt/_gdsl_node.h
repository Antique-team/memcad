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
 * $RCSfile: _gdsl_node.h,v $
 * $Revision: 1.22 $
 * $Date: 2006/03/04 16:32:05 $
 */


#ifndef __GDSL_NODE_H_
#define __GDSL_NODE_H_

#ifndef MEMCAD_INRIA
#include <stdio.h>
#endif /* MEMCAD_INRIA */

#include "gdsl_types.h"


#ifdef __cplusplus
extern "C" 
{
#endif /* __cplusplus */

// FBR: copied here from _gdsl_node.c for memcad
typedef struct _gdsl_node
{
    struct _gdsl_node* succ;    /* Node's successor */
    struct _gdsl_node* pred;    /* Node's predecessor */
    gdsl_element_t     content; /* Node's content */
} _gdsl_node;

/**
 * @defgroup _gdsl_node Low-level doubly-linked node manipulation module
 * @{
 */

/**
 * @brief GDSL low-level doubly linked node type.
 *
 * This type is voluntary opaque. Variables of this kind could'nt be directly
 * used, but by the functions of this module.
 */
typedef struct _gdsl_node* _gdsl_node_t;

/**
 * @brief GDSL low-level doubly-linked node map function type.
 * @param NODE The low-level node to map.
 * @param USER_DATA The user datas to pass to this function.
 * @return GDSL_MAP_STOP if the mapping must be stopped.
 * @return GDSL_MAP_CONT if the mapping must be continued.
 */  
typedef int (* _gdsl_node_map_func_t) (const _gdsl_node_t NODE,
				       void* USER_DATA
				       );

/**
 * @brief GDSL low-level doubly-linked node write function type.
 * @param TREE The low-level doubly-linked node to write.
 * @param OUTPUT_FILE The file where to write NODE.
 * @param USER_DATA The user datas to pass to this function.
 */
/* typedef void (* _gdsl_node_write_func_t) (const _gdsl_node_t NODE, */
/* 					  FILE* OUTPUT_FILE, */
/* 					  void* USER_DATA */
/* 					  ); */

/******************************************************************************/
/* Management functions of low-level doubly linked nodes                      */
/******************************************************************************/

/**
 * @brief Create a new low-level node.
 *
 * Allocate a new low-level node data structure.
 *
 * @note Complexity: O( 1 )
 * @pre nothing.
 * @return the newly allocated low-level node in case of success.
 * @return NULL in case of insufficient memory.
 * @see _gdsl_node_free()
 */
extern _gdsl_node_t
_gdsl_node_alloc (void);

/**
 * @brief Destroy a low-level node.
 *
 * Deallocate the low-level node NODE.
 *
 * @note O( 1 )
 * @pre NODE != NULL
 * @return the content of NODE (without modification).
 * @see _gdsl_node_alloc()
 */
extern gdsl_element_t
_gdsl_node_free (_gdsl_node_t NODE
		 );

/******************************************************************************/
/* Consultation functions of low-level doubly linked nodes                    */
/******************************************************************************/

/**
 * @brief Get the successor of a low-level node.
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which we want to get the successor from.
 * @return the sucessor of the low-level node NODE if NODE has a successor.
 * @return NULL if the low-level node NODE has no successor.
 * @see _gdsl_node_get_pred()
 * @see _gdsl_node_set_succ()
 * @see _gdsl_node_set_pred()
 */
extern _gdsl_node_t
_gdsl_node_get_succ (const _gdsl_node_t NODE
		     );

/**
 * @brief Get the predecessor of a low-level node.
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which we want to get the predecessor from.
 * @return the predecessor of the low-level node NODE if NODE has a predecessor.
 * @return NULL if the low-level node NODE has no predecessor.
 * @see _gdsl_node_get_succ()
 * @see _gdsl_node_set_succ()
 * @see _gdsl_node_set_pred()
 */
extern _gdsl_node_t
_gdsl_node_get_pred (const _gdsl_node_t NODE
		     );

/**
 * @brief Get the content of a low-level node.
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which we want to get the content from.
 * @return the content of the low-level node NODE if NODE has a content.
 * @return NULL if the low-level node NODE has no content.
 * @see _gdsl_node_set_content()
 */
extern gdsl_element_t
_gdsl_node_get_content (const _gdsl_node_t NODE
			);

/******************************************************************************/
/* Modification functions of low-level doubly linked nodes                    */
/******************************************************************************/

/**
 * @brief Set the successor of a low-level node.
 *
 * Modifie the sucessor of the low-level node NODE to SUCC.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which want to change the successor from.
 * @param SUCC The new successor of NODE.
 * @see _gdsl_node_get_succ()
 */
extern void
_gdsl_node_set_succ (_gdsl_node_t NODE,
		     const _gdsl_node_t SUCC
		     );

/**
 * @brief Set the predecessor of a low-level node.
 *
 * Modifie the predecessor of the low-level node NODE to PRED.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which want to change the predecessor from.
 * @param PRED The new predecessor of NODE.
 * @see _gdsl_node_get_pred()
 */
extern void
_gdsl_node_set_pred (_gdsl_node_t NODE,
		     const _gdsl_node_t PRED
		     );

/**
 * @brief Set the content of a low-level node.
 *
 * Modifie the content of the low-level node NODE to CONTENT.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL
 * @param NODE The low-level node which want to change the content from.
 * @param CONTENT The new content of NODE.
 * @see _gdsl_node_get_content()
 */
extern void
_gdsl_node_set_content (_gdsl_node_t NODE,
			const gdsl_element_t CONTENT
			);

/**
 * @brief Link two low-level nodes together.
 *
 * Link the two low-level nodes NODE1 and NODE2 together.
 * After the link, NODE1's successor is NODE2 and NODE2's predecessor is NODE1.
 *
 * @note Complexity: O( 1 )
 * @pre NODE1 != NULL & NODE2 != NULL
 * @param NODE1 The first low-level node to link to NODE2.
 * @param NODE2 The second low-level node to link from NODE1.
 * @see _gdsl_node_unlink()
 */
extern void
_gdsl_node_link (_gdsl_node_t NODE1,
		 _gdsl_node_t NODE2
		 );

/**
 * @brief Unlink two low-level nodes.
 *
 * Unlink the two low-level nodes NODE1 and NODE2. 
 * After the unlink, NODE1's successor is NULL and NODE2's predecessor is NULL.
 *
 * @note Complexity: O( 1 )
 * @pre NODE1 != NULL & NODE2 != NULL
 * @param NODE1 The first low-level node to unlink from NODE2.
 * @param NODE2 The second low-level node to unlink from NODE1.
 * @see _gdsl_node_link()
 */
extern void
_gdsl_node_unlink (_gdsl_node_t NODE1,
		   _gdsl_node_t NODE2
		   );

/******************************************************************************/
/* Input/output functions of low-level doubly linked nodes                    */
/******************************************************************************/

/**
 * @brief Write a low-level node to a file.
 *
 * Write the low-level node NODE to OUTPUT_FILE, using WRITE_F function.
 * Additionnal USER_DATA argument could be passed to WRITE_F.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL & WRITE_F != NULL & OUTPUT_FILE != NULL
 * @param NODE The low-level node to write.
 * @param WRITE_F The write function.
 * @param OUTPUT_FILE The file where to write NODE.
 * @param USER_DATA User's datas passed to WRITE_F.
 * @see _gdsl_node_write_xml()
 * @see _gdsl_node_dump()
 */
extern void
_gdsl_node_write (const _gdsl_node_t NODE,
		  FILE* OUTPUT_FILE,
		  void* USER_DATA
		  );

/**
 * @brief Write a low-level node to a file into XML.
 *
 * Write the low-level node NODE to OUTPUT_FILE, into XML language.
 * If WRITE_F != NULL, then uses WRITE_F function to write NODE to OUTPUT_FILE.
 * Additionnal USER_DATA argument could be passed to WRITE_F.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL & OUTPUT_FILE != NULL
 * @param NODE The low-level node to write.
 * @param WRITE_F The write function.
 * @param OUTPUT_FILE The file where to write NODE.
 * @param USER_DATA User's datas passed to WRITE_F.
 * @see _gdsl_node_write()
 * @see _gdsl_node_dump()
 */
extern void
_gdsl_node_write_xml (const _gdsl_node_t NODE,
		      FILE* OUTPUT_FILE,
		      void* USER_DATA
		      );

/**
 * @brief Dump the internal structure of a low-level node to a file.
 *
 * Dump the structure of the low-level node NODE to OUTPUT_FILE. 
 * If WRITE_F != NULL, then uses WRITE_F function to write NODE to OUTPUT_FILE.
 * Additionnal USER_DATA argument could be passed to WRITE_F.
 *
 * @note Complexity: O( 1 )
 * @pre NODE != NULL & OUTPUT_FILE != NULL
 * @param NODE The low-level node to dump.
 * @param WRITE_F The write function.
 * @param OUTPUT_FILE The file where to write NODE.
 * @param USER_DATA User's datas passed to WRITE_F.
 * @see _gdsl_node_write()
 * @see _gdsl_node_write_xml()
 */
extern void
_gdsl_node_dump (const _gdsl_node_t NODE,
		 FILE* OUTPUT_FILE,
		 void* USER_DATA
		 );


/*
 * @}
 */


#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* __GDSL_NODE_H_ */


/** EMACS **
 * Local variables:
 * mode: c
 * c-basic-offset: 4
 * End:
 */
