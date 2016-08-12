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
 * $RCSfile: _gdsl_node.c,v $
 * $Revision: 1.11 $
 * $Date: 2006/03/04 16:32:05 $
 */

#include "gdsl_config.h"

#ifndef MEMCAD_INRIA
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#endif /* MEMCAD_INRIA */

#include "_gdsl_node.h"
#include "gdsl_types.h"


/* struct _gdsl_node */
/* { */
/*     struct _gdsl_node* succ;    /\* Node's successor *\/ */
/*     struct _gdsl_node* pred;    /\* Node's predecessor *\/ */
/*     gdsl_element_t     content; /\* Node's content *\/ */
/* }; */

/******************************************************************************/
/* Management functions of low-level doubly linked nodes                      */
/******************************************************************************/

extern _gdsl_node_t
_gdsl_node_alloc (void)
{
    _gdsl_node_t n;

    n = (_gdsl_node_t) malloc (sizeof (struct _gdsl_node));

    if (n == NULL)
	{
	    return NULL;
	}

    n->content = NULL;
    n->succ    = NULL;
    n->pred    = NULL;

    return n;
}

extern gdsl_element_t
_gdsl_node_free (_gdsl_node_t n)
{
    gdsl_element_t e;

    assert (n != NULL);

    e = n->content;
    free (n);

    return e;
}

/******************************************************************************/
/* Consultation functions of low-level doubly linked nodes                    */
/******************************************************************************/

extern _gdsl_node_t
_gdsl_node_get_succ (const _gdsl_node_t n)
{
    assert (n != NULL);

    return n->succ;
}

extern _gdsl_node_t
_gdsl_node_get_pred (const _gdsl_node_t n)
{
    assert (n != NULL);

    return n->pred;
}

extern gdsl_element_t
_gdsl_node_get_content (const _gdsl_node_t n)
{
    assert (n != NULL);

    return n->content;
}

/******************************************************************************/
/* Modification functions of low-level doubly linked nodes                    */
/******************************************************************************/

extern void
_gdsl_node_set_succ (_gdsl_node_t n, const _gdsl_node_t succ)
{
    assert (n != NULL);

    n->succ = succ;
}

extern void
_gdsl_node_set_pred (_gdsl_node_t n, const _gdsl_node_t pred)
{
    assert (n != NULL);

    n->pred = pred;
}

extern void
_gdsl_node_set_content (_gdsl_node_t n, const gdsl_element_t e)
{
    assert (n != NULL);

    n->content = e;
}

extern void
_gdsl_node_link (_gdsl_node_t node1, _gdsl_node_t node2)
{
    assert (node1 != NULL);
    assert (node2 != NULL);

    node1->succ = node2;
    node2->pred = node1;
}

extern void
_gdsl_node_unlink (_gdsl_node_t node1, _gdsl_node_t node2)
{
    assert (node1 != NULL);
    assert (node2 != NULL);

    node1->succ = NULL;
    node2->pred = NULL;
}

/******************************************************************************/
/* Input/output functions of low-level doubly linked nodes                    */
/******************************************************************************/

extern void
_gdsl_node_write (const _gdsl_node_t n, FILE* file, void* user_data)
{
    assert (n != NULL);
    assert (file != NULL);

    write_f (n, file, user_data);
}

extern void
_gdsl_node_write_xml (const _gdsl_node_t n, 
		      FILE* file, 
		      void* user_data)
{
    assert (n != NULL);
    assert (file != NULL);

    fprintf (file, "<_GDSL_NODE REF=\"%p\"", (void*) n);

    if (n->succ != NULL)
	{
	    fprintf (file, " SUCC=\"%p\"", (void*) n->succ);
	}
    else
	{
	    fprintf (file, " SUCC=\"\"");
	}
  
    if (n->pred != NULL)
	{
	    fprintf (file, " PRED=\"%p\">", (void*) n->pred);
	}
    else
	{
	    fprintf (file, " PRED=\"\">");
	}
  
    write_f (n, file, user_data);
  
    fprintf (file, "</_GDSL_NODE>\n");
}

extern void
_gdsl_node_dump (const _gdsl_node_t n,
		 FILE* file, void* user_data)
{
    assert (n != NULL);
    assert (file != NULL);

    fprintf (file, "<_GDSL_NODE REF=\"%p\"", (void*) n);
  
    if (n->content != NULL)
	{
	    fprintf (file, " CONTENT=\"%p\"", (void*) n->content);
	}
    else
	{
	    fprintf (file, " CONTENT=\"\"");
	}

    if (n->succ != NULL)
	{
	    fprintf (file, " SUCC=\"%p\"", (void*) n->succ);
	}
    else
	{
	    fprintf (file, " SUCC=\"\"");
	}

    if (n->pred != NULL)
	{
	    fprintf (file, " PRED=\"%p\">", (void*) n->pred);
	}
    else
	{
	    fprintf (file, " PRED=\"\">");
	}

    write_f (n, file, user_data);

    fprintf (file, "</_GDSL_NODE>\n");
}


/** EMACS **
 * Local variables:
 * mode: c
 * c-basic-offset: 4
 * End:
 */
