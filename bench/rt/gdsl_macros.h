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
 * $RCSfile: gdsl_macros.h,v $
 * $Revision: 1.13 $
 * $Date: 2006/03/04 16:32:05 $
 */


#ifndef _GDSL_MACROS_H_
#define _GDSL_MACROS_H_


#ifdef __cplusplus
extern "C" 
{
#endif /* __cplusplus */


/**
 * @defgroup gdsl_macros Various macros module
 * @{
 */

#ifdef GDSL_MAX
#undef GDSL_MAX
#endif

/**
 * @brief Give the greatest number of two numbers.
 *
 * @note Complexity: O( 1 )
 * @pre X & Y must be basic scalar C types
 * @param X First scalar variable
 * @param Y Second scalar variable
 * @return X if X is greather than Y.
 * @return Y if Y is greather than X.
 * @see GDSL_MIN()
 */
#define GDSL_MAX(X,Y) (X>Y?X:Y)

#ifdef GDSL_MIN
#undef GDSL_MIN
#endif

/**
 * @brief Give the lowest number of two numbers
 *
 * @note Complexity: O( 1 )
 * @pre X & Y must be basic scalar C types
 * @param X First scalar variable
 * @param Y Second scalar variable
 * @return Y if Y is lower than X.
 * @return X if X is lower than Y.
 * @see GDSL_MAX()
 */
#define GDSL_MIN(X,Y) (X>Y?Y:X)


/*
 * @}
 */


#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* _GDSL_MACROS_H_ */


/** EMACS **
 * Local variables:
 * mode: c
 * c-basic-offset: 4
 * End:
 */
