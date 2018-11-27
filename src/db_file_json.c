/* aide, Advanced Intrusion Detection Environment
 *
 * Copyright (C) 1999-2007,2010-2013,2016 Rami Lehti, Pablo Virolainen, Mike
 * Markley, Richard van den Berg, Hannes von Haugwitz
 * $Header$
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include "aide.h"
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdlib.h>
#include <time.h>

#include <errno.h>

#include "types.h"
#include "base64.h"
#include "db_file_json.h"
#include "gen_list.h"
#include "conf_yacc.h"
#include "util.h"
#include "commandconf.h"
/*for locale support*/
#include "locale-aide.h"
/*for locale support*/

#ifdef WITH_MHASH
#include <mhash.h>
#endif

#ifdef WITH_ZLIB
#include <zlib.h>
#endif

#define BUFSIZE 16384

#include "md.h"

#ifdef WITH_ZLIB
#define ZBUFSIZE 16384

/*
static int dofprintf_ram( const char* s,...)
#ifdef __GNUC__
        __attribute__ ((format (printf, 1, 2)));
#else
        ;
#endif
*/

RamLine* NewRamLine()
{
        RamLine * line = (RamLine*)malloc(sizeof(RamLine));
        line->size = RAMLINE_BLOCK_SIZE;
        line->data = (unsigned char *)calloc(RAMLINE_BLOCK_SIZE, 1);
        line->rwPos = line->data;

        return line;
}

int resizeRamLine(RamLine *out, unsigned int newAppendLen)
{
        unsigned int oldDataLen = RAMLINE_LEN(out);
        unsigned int newAddLen = ((newAppendLen + RAMLINE_BLOCK_SIZE) % RAMLINE_BLOCK_SIZE) * RAMLINE_BLOCK_SIZE;

        unsigned char* newData = (unsigned char*)calloc(oldDataLen + newAddLen, 1);
        memcpy(newData, out->data, oldDataLen);
        free(out->data);
        out->data = newData;
        out->rwPos = out->data + newAddLen;
        out->size = out->size + newAddLen;

        return 0;
}

int ramLineWrite(RamLine *out, unsigned char * buf, unsigned int len)
{
        if(out == NULL)
        {
                return -1;
        }

        if(len > RAMLINE_BUF_LEN(out))
        {
                resizeRamLine(out, len);
        }

        memcpy(out->rwPos, buf, len);
        out->rwPos = out->rwPos + len;

        return 0;
}

#endif

int dofprintf_ram(char ** dst, const char* s,...)
{
    char buf[3];
    int retval;
    char* temp=NULL;
    va_list ap;

    va_start(ap,s);
    retval=vsnprintf(buf,3,s,ap);
    va_end(ap);

    temp=(char*)calloc(retval+2, 1);
    if(temp==NULL)
    {
        error(0,"Unable to alloc %i bytes\n",retval+2);
        return -1;
    }

    va_start(ap,s);
    retval=vsnprintf(temp,retval+1,s,ap);
    va_end(ap);


    *dst = temp;
    return retval;
}

int db_writeint_ram(char ** dst, long i)
{
    return dofprintf_ram(dst, "%li",i);
}

int db_writelong_ram(char ** dst, AIDE_OFF_TYPE i)
{
#if defined HAVE_OFF64_TYPE && SIZEOF_OFF64_T == SIZEOF_LONG_LONG || !defined HAVE_OFF64_TYPE && SIZEOF_OFF_T == SIZEOF_LONG_LONG
    return dofprintf_ram(dst, "%lli",(long long)i);
#else
    return dofprintf_ram(dst, "%li",i);
#endif
}

int db_write_byte_base64_ram(char **dst, byte*data,size_t len, DB_ATTR_TYPE th, DB_ATTR_TYPE attr )
{
    char* tmpstr=NULL;
    int retval=0;

    if (data && !len)
        len = strlen((const char *)data);

    if (data!=NULL&&th&attr)
    {
        tmpstr=encode_base64(data,len);
    }
    else
    {
        tmpstr=NULL;
    }

    if(tmpstr)
    {
        retval=dofprintf_ram(dst, "%s", tmpstr);
        free(tmpstr);
        return retval;
    }
    else
    {
        return dofprintf_ram(dst, "0");
    }
    return 0;
}

int db_write_time_base64_ram(char **dst, time_t i)
{
    static char* ptr=NULL;
    char* tmpstr=NULL;
    int retval=0;

    if(i==0)
    {
        retval=dofprintf_ram(dst, "0");
        return retval;
    }


    ptr=(char*)malloc(sizeof(char)*TIMEBUFSIZE);
    if (ptr==NULL)
    {
        error(0,"\nCannot allocate memory.\n");
        abort();
    }
    memset((void*)ptr,0,sizeof(char)*TIMEBUFSIZE);

    sprintf(ptr,"%li",i);


    tmpstr=encode_base64((byte *)ptr,strlen(ptr));
    retval=dofprintf_ram(dst, "%s", tmpstr);
    free(tmpstr);
    free(ptr);

    return retval;
}

int db_writeoct_ram(char **dst, long i)
{
    return dofprintf_ram(dst, "%lo",i);
}

// JSON DB

JsonDB* dbJSON_New(int isDump2File, unsigned char *filePath)
{
    JsonDB * jDB = (JsonDB*)calloc(sizeof(JsonDB), 1);
    jDB->isDump2File = isDump2File == 0 ? 0 : 1;

    if(jDB->isDump2File)
    {
        strcpy(jDB->filePath, filePath);
    }

    jDB->db = cJSON_CreateObject();
    if(jDB->db == NULL)
    {
        return NULL;
    }

    jDB->fileList = cJSON_AddArrayToObject(jDB->db, "filsDB");

    return jDB;
}

int dbJSON_writespec(JsonDB *jDB, db_config* conf)
{
    char * jDBStr = NULL;
    int ret = 0;
    int idx = 0;
    cJSON * spec = cJSON_CreateObject();
    cJSON * specItems = NULL;

    if(cJSON_AddNumberToObject(spec, "itemsCount", conf->db_out_size) == NULL)
    {
        goto end;
    }

    specItems = cJSON_AddArrayToObject(spec, "items");
    if(specItems == NULL)
    {
        goto end;
    }

    /*
    fprintf(stdout, "\n+++ dbJSON_writespe() cout cnt:%d out items:", conf->db_out_size);
    for (idx = 0; idx < conf->db_out_size; idx++)
    {
        fprintf(stdout," %d", conf->db_out_order[idx]);
    }
    fprintf(stdout,"\n");
    */

    for(idx = 0; idx < conf->db_out_size; idx++)
    {
        int fieldIdx = conf->db_out_order[idx];
        cJSON *item = cJSON_CreateString(db_field_names[fieldIdx]);
        if(item == NULL)
        {
            goto end;
        }

        cJSON_AddItemToArray(specItems, item);
    }

    cJSON_AddItemToObject(jDB->db, "spec", spec);

    /*
    jDBStr = cJSON_Print(jDB->db);
    fprintf(stdout, "\n=== dbJSON_writespe() obj:\n%s\n\n", jDBStr);
    free(jDBStr);
    */


    return 0;

end:
    cJSON_Delete(spec);
    return -1;
}

cJSON * dbJSON_line2FileObject(db_line* line, db_config* dbconf)
{
    int i;
    cJSON * item = NULL;
    cJSON * fileObj = cJSON_CreateObject();

    for(i=0;i<dbconf->db_out_size;i++)
    //for(i=0;i<6;i++)
    {
        switch (dbconf->db_out_order[i])
        {
            case db_filename :
            {
                //db_writechar(line->filename,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddStringToObject(fileObj, db_field_names[db_filename], line->filename) == NULL)
                    goto  end;
                break;
            }
            case db_linkname :
            {
                //db_writechar(line->linkname,(FILE*)dbconf->dbc_out.dbP,i);
                char * lname = line->linkname == NULL ? "0" : line->linkname;
                if(cJSON_AddStringToObject(fileObj, db_field_names[db_linkname], lname) == NULL)
                    goto  end;
                break;
            }
            case db_bcount :
            {
                //db_writeint(line->bcount,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_bcount], line->bcount) == NULL)
                    goto  end;
                break;
            }
            case db_mtime :
            {
                //db_write_time_base64(line->mtime,(FILE*)dbconf->dbc_out.dbP,i);
                char * dst = NULL;
                int ret = db_write_time_base64_ram(&dst, line->mtime);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_mtime ], dst) == NULL)
                {
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                if(dst != NULL)
                    free(dst);
                break;
            }
            case db_atime :
            {
                //db_write_time_base64(line->atime,(FILE*)dbconf->dbc_out.dbP,i);
                char * dst = NULL;
                int ret = db_write_time_base64_ram(&dst, line->atime);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_atime ], dst) == NULL)
                {
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                if(dst != NULL)
                    free(dst);
                break;
            }
            case db_ctime :
            {
                //db_write_time_base64(line->ctime,(FILE*)dbconf->dbc_out.dbP,i);
                char * dst = NULL;
                int ret = db_write_time_base64_ram(&dst, line->ctime);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_ctime ], dst) == NULL)
                {
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                if(dst != NULL)
                    free(dst);
                break;
            }
            case db_inode :
            {
                //db_writeint(line->inode,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_inode], line->inode) == NULL)
                    goto  end;
                break;
            }
            case db_lnkcount :
            {
                //db_writeint(line->nlink,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_lnkcount], line->nlink) == NULL)
                    goto  end;
                break;
            }
            case db_uid :
            {
                //db_writeint(line->uid,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_uid], line->uid) == NULL)
                    goto  end;
                break;
            }
            case db_gid :
            {
                //db_writeint(line->gid,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_gid], line->gid) == NULL)
                    goto  end;
                break;
            }
            case db_size :
            {
                //db_writelong(line->size,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_size], line->size) == NULL)
                    goto  end;
                break;
            }
            case db_md5 :
            {
                //db_write_byte_base64(line->md5, HASH_MD5_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_MD5,line->attr);
                char * str = db_write_byte_base64_str(line->md5, HASH_MD5_LEN, i, DB_MD5,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_md5], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_sha1 :
            {
                //db_write_byte_base64(line->sha1, HASH_SHA1_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_SHA1,line->attr);
                char * str = db_write_byte_base64_str(line->sha1, HASH_SHA1_LEN, i, DB_SHA1,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_sha1], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_rmd160 :
            {
                //db_write_byte_base64(line->rmd160, HASH_RMD160_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_RMD160,line->attr);
                char * str = db_write_byte_base64_str(line->rmd160, HASH_RMD160_LEN, i, DB_RMD160,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_rmd160], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_tiger :
            {
                //db_write_byte_base64(line->tiger, HASH_TIGER_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_TIGER,line->attr);
                char * str = db_write_byte_base64_str(line->tiger, HASH_TIGER_LEN, i, DB_TIGER,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_tiger], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_perm :
            {
                //fprintf(stdout,"++++++++++++++++++++++++++++++++++++++++++++++++++++++ db_perm\n");
                //break;
                //db_writeoct(line->perm,(FILE*)dbconf->dbc_out.dbP,i);
                char * dst = NULL;
                int ret = db_writeoct_ram(&dst, line->perm);
                //fprintf(stdout,"+++ ret:%d dst:%s\n", ret, dst);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_perm], dst) == NULL)
                {
                    //fprintf(stdout,"+++ ret:%d dst:%s\n", ret, dst);
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                //fprintf(stdout,"+++ ret:%d dst:%s\n", ret, dst);
                if(dst != NULL)
                    free(dst);
                break;
            }
            case db_crc32 :
            {
                //db_write_byte_base64(line->crc32, HASH_CRC32_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_CRC32,line->attr);
                char * str = db_write_byte_base64_str(line->crc32, HASH_CRC32_LEN, i, DB_CRC32,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_crc32], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_crc32b :
            {
                //db_write_byte_base64(line->crc32b, HASH_CRC32B_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_CRC32B,line->attr);
                char * str = db_write_byte_base64_str(line->crc32b, HASH_CRC32B_LEN, i, DB_CRC32B,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_crc32b], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_haval :
            {
                //db_write_byte_base64(line->haval, HASH_HAVAL256_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_HAVAL,line->attr);
                char * str = db_write_byte_base64_str(line->haval, HASH_HAVAL256_LEN, i, DB_HAVAL,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_haval], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_gost :
            {
                //db_write_byte_base64(line->gost , HASH_GOST_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_GOST,line->attr);
                char * str = db_write_byte_base64_str(line->gost , HASH_GOST_LEN, i, DB_GOST,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_gost], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_sha256 :
            {
                //db_write_byte_base64(line->sha256, HASH_SHA256_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_SHA256,line->attr);
                char * str = db_write_byte_base64_str(line->sha256, HASH_SHA256_LEN, i, DB_SHA256,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_sha256], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_sha512 :
            {
                //db_write_byte_base64(line->sha512, HASH_SHA512_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_SHA512,line->attr);
                char * str = db_write_byte_base64_str(line->sha512, HASH_SHA512_LEN, i, DB_SHA512,line->attr);

                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_sha512], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_whirlpool :
            {
                //db_write_byte_base64(line->whirlpool, HASH_WHIRLPOOL_LEN, (FILE*)dbconf->dbc_out.dbP,i, DB_WHIRLPOOL,line->attr);
                char * str = db_write_byte_base64_str(line->whirlpool, HASH_WHIRLPOOL_LEN, i, DB_WHIRLPOOL,line->attr);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_whirlpool], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
            case db_attr :
            {
                //db_writelong(line->attr, (FILE*)dbconf->dbc_out.dbP,i);
                char * dst = NULL;
                int ret = db_writelong_ram(&dst, line->attr);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_attr], dst) == NULL)
                {
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                if(dst != NULL)
                    free(dst);
                break;
            }
#ifdef WITH_ACL
            case db_acl :
            {
                //Does not support now
                /*
                db_writeacl(line->acl,(FILE*)dbconf->dbc_out.dbP,i);
                */
                break;
            }
#endif
            case db_xattrs :
            {
                // Does not support now
                /*
                xattr_node *xattr = NULL;
                size_t num = 0;

                if (!line->xattrs)
                {
                    db_writelong(0, (FILE*)dbconf->dbc_out.dbP, i);
                    break;
                }

                db_writelong(line->xattrs->num, (FILE*)dbconf->dbc_out.dbP, i);

                xattr = line->xattrs->ents;
                while (num < line->xattrs->num)
                {
                    dofprintf(",");
                    db_writechar(xattr->key, (FILE*)dbconf->dbc_out.dbP, 0);
                    dofprintf(",");
                    db_write_byte_base64(xattr->val, xattr->vsz, (FILE*)dbconf->dbc_out.dbP, 0, 1, 1);

                    ++xattr;
                    ++num;
                }
                */
                break;
            }
            case db_selinux :
            {
                //db_write_byte_base64((byte*)line->cntx, 0, (FILE*)dbconf->dbc_out.dbP, i, 1, 1);
                char * str = db_write_byte_base64_str((byte*)line->cntx, 0, (FILE*)dbconf->dbc_out.dbP, i, 1, 1);
                if(str == NULL)
                    goto end;

                if(cJSON_AddStringToObject(fileObj, db_field_names[db_md5], str) == NULL)
                {
                    free(str);
                    goto end;
                }
                break;
            }
#ifdef WITH_E2FSATTRS
            case db_e2fsattrs :
            {
                //db_writelong(line->e2fsattrs,(FILE*)dbconf->dbc_out.dbP,i);
                if(cJSON_AddNumberToObject(fileObj, db_field_names[db_e2fsattrs], line->e2fsattrs) == NULL)
                    goto  end;
                break;
            }
#endif
            case db_checkmask :
            {
                //db_writeoct(line->attr,(FILE*)dbconf->dbc_out.dbP,i);
                char *dst = NULL;
                int ret = db_writeoct(&dst, line->attr);
                if(ret <= 0 || cJSON_AddStringToObject(fileObj, db_field_names[db_checkmask], dst) == NULL)
                {
                    if(dst != NULL)
                        free(dst);
                    goto  end;
                }
                if(dst != NULL)
                    free(dst);
                break;
            }
            default :
            {
                error(0,"Not implemented in db_writeline_file %i\n", dbconf->db_out_order[i]);
                //return RETFAIL;
                return NULL;
            }
        }
    }

    return fileObj;

end:
    fprintf(stdout,"+++++++ dbJSON_line2FileObject() fail at i:%d name:%s\n", i, db_field_names[i]);
    cJSON_Delete(fileObj);
    return NULL;
}

int dbJSON_writeFileObject(JsonDB *jDB, db_line* line, db_config* dbconf)
{
    cJSON * fileObj = dbJSON_line2FileObject(line, dbconf);
    if(fileObj != NULL)
    {
        fprintf(stdout,"+++ got JSON file obj +++\n");
        cJSON_AddItemToArray(jDB->fileList, fileObj);
    }
    return 0;
}

int dbJSON_close(JsonDB * jDB)
{

    cJSON_Delete(jDB->db);
    return 0;
}




