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
#include "db_file_ram.h"
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

static int dofprintf_ram( const char* s,...)
#ifdef __GNUC__
        __attribute__ ((format (printf, 1, 2)));
#else
        ;
#endif

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


int dofflush_ram(void)
{

  int retval;
#ifdef WITH_ZLIB
  if(conf->gzip_dbout){
    /* Should not flush using gzip, it degrades compression */
    retval=Z_OK;
  }else {
#endif
    //retval=fflush(conf->db_out); 
#ifdef WITH_ZLIB
  }
#endif

  return retval;
}

int dofprintf_ram( const char* s,...)
{
  char buf[3];
  int retval;
  char* temp=NULL;
  va_list ap;
  
  va_start(ap,s);
  retval=vsnprintf(buf,3,s,ap);
  va_end(ap);
  
  temp=(char*)malloc(retval+2);
  if(temp==NULL){
    error(0,"Unable to alloc %i bytes\n",retval+2);
    return -1;
  }  
  va_start(ap,s);
  retval=vsnprintf(temp,retval+1,s,ap);
  va_end(ap);
  
  if (conf->mdc_out) {
      update_md(conf->mdc_out,temp ,retval);
  }

#ifdef WITH_MHASH
  if(conf->do_dbnewmd)
    mhash(conf->dbnewmd,(void*)temp,retval);
#endif

#ifdef WITH_ZLIB
  if(conf->gzip_dbout){
    retval=gzwrite(conf->db_gzout,temp,retval);
  }else{
#endif
    /* writing is ok with fwrite with curl.. */
    retval=fwrite(temp,1,retval,conf->db_out);
#ifdef WITH_ZLIB
  }
#endif
  free(temp);

  return retval;
}



int db_file_read_spec_ram(int db)
{
  
  int i=0;
  int* db_osize=0;
  DB_FIELD** db_order=NULL;

  switch (db) {
  case DB_OLD: {
    db_osize=&(conf->db_in_size);
    db_order=&(conf->db_in_order);
    db_lineno=&db_in_lineno;
    break;
  }
  case DB_NEW: {
    db_osize=&(conf->db_new_size);
    db_order=&(conf->db_new_order);
    db_lineno=&db_new_lineno;
    break;
  }
  }

  *db_order=(DB_FIELD*) malloc(1*sizeof(DB_FIELD));
  
  while ((i=db_scan())!=TNEWLINE){
    switch (i) {
      
    case TID : {
      int l;
      

      /* Yes... we do not check if realloc returns nonnull */

      *db_order=(DB_FIELD*)
	realloc((void*)*db_order,
		((*db_osize)+1)*sizeof(DB_FIELD));
      
      if(*db_order==NULL){
	return RETFAIL;
      }
      
      (*db_order)[*db_osize]=db_unknown;
      
      for (l=0;l<db_unknown;l++){
	
	if (strcmp(db_names[l],dbtext)==0) {
	  
	  if (check_db_order(*db_order, *db_osize,
			     db_value[l])==RETFAIL) {
	    error(0,"Field %s redefined in @@dbspec\n",dbtext);
	    (*db_order)[*db_osize]=db_unknown;
	  } else {
	    (*db_order)[*db_osize]=db_value[l];
	  }
	  (*db_osize)++;
	  break;
	}
      }
      for (l=0;l<db_alias_size;l++){
	
	if (strcmp(db_namealias[l],dbtext)==0) {
	  
	  if (check_db_order(*db_order, *db_osize,
			     db_aliasvalue[l])==RETFAIL) {
	    error(0,"Field %s redefined in @@dbspec\n",dbtext);
	    (*db_order)[*db_osize]=db_unknown;
	  } else {
	    (*db_order)[*db_osize]=db_aliasvalue[l];
	  }
	  (*db_osize)++;
	  break;
	}
      }
      if(l==db_unknown){
	error(0,"Unknown field %s in database\n",dbtext);
	(*db_osize)++;
      }
      break;
    }
    
    case TDBSPEC : {
      error(0,"Only one @@dbspec in input database.\n");
      return RETFAIL;
      break;
    }
    
    default : {
      error(0,"Aide internal error while reading input database.\n");
      return RETFAIL;
    }
    }
  }

  /* Lets generate attr from db_order if database does not have attr */
  conf->attr=-1;

  for (i=0;i<*db_osize;i++) {
    if ((*db_order)[i]==db_attr) {
      conf->attr=1;
    }
  }
  if (conf->attr==DB_ATTR_UNDEF) {
    conf->attr=0;
    error(0,"Database does not have attr field.\nComparation may be incorrect\nGenerating attr-field from dbspec\nIt might be a good Idea to regenerate databases. Sorry.\n");
    for(i=0;i<conf->db_in_size;i++) {
      conf->attr|=1<<(*db_order)[i];
    }
  }
  return RETOK;
}

char** db_readline_file_ram(int db)
{
  
  char** s=NULL;
  
  int i=0;
  int r;
  int a=0;
  int token=0;
  int gotbegin_db=0;
  int gotend_db=0;
  int* domd=NULL;
#ifdef WITH_MHASH
  MHASH* md=NULL;
#endif
  char** oldmdstr=NULL;
  int* db_osize=0;
  DB_FIELD** db_order=NULL;
  FILE** db_filep=NULL;
  url_t* db_url=NULL;

  switch (db) {
  case DB_OLD: {
#ifdef WITH_MHASH
    md=&(conf->dboldmd);
#endif
    domd=&(conf->do_dboldmd);
    oldmdstr=&(conf->old_dboldmdstr);
    
    db_osize=&(conf->db_in_size);
    db_order=&(conf->db_in_order);
    db_filep=&(conf->db_in);
    db_url=conf->db_in_url;
    db_lineno=&db_in_lineno;
    break;
  }
  case DB_NEW: {
#ifdef WITH_MHASH
    md=&(conf->dbnewmd);
#endif
    domd=&(conf->do_dbnewmd);
    oldmdstr=&(conf->old_dbnewmdstr);
    
    db_osize=&(conf->db_new_size);
    db_order=&(conf->db_new_order);
    db_filep=&(conf->db_new);
    db_url=conf->db_new_url;
    db_lineno=&db_new_lineno;
    break;
  }
  }
  
  if (*db_osize==0) {
    db_buff(db,*db_filep);
    
    token=db_scan();
    while((token!=TDBSPEC && token!=TEOF)){

      switch(token){
      case TUNKNOWN: {
	continue;
      }
      case TBEGIN_DB: {
	token=db_scan();
	gotbegin_db=1;
	continue;
      }
      case TNEWLINE: {
	if(gotbegin_db){
	  *domd=1;
	  token=db_scan();
	  continue;
	}else {
	  token=TEOF;
	  break;
	}
      }
      case TGZIPHEADER: {
	error(0,"Gzipheader found inside uncompressed db!\n");
	return NULL;
      }
      default: {
	/* If it is anything else we quit */
	/* Missing dbspec */
	token=TEOF;
	break;
      }
      }
    }

    if(FORCEDBMD&&!gotbegin_db){
      error(0,"Database %i does not have checksum!\n",db);
      return NULL;
    }

    if (token!=TDBSPEC) {
      /*
       * error.. must be a @@dbspec line
       */
      
      switch (db_url->type) {
      case url_file : {
	error(0,"File database must have one db_spec specification\n");
	break;
      }

      case url_stdin : {
	error(0,"Pipe database must have one db_spec specification\n");
	break;
      }

      case url_fd: {
	error(0,"FD database must have one db_spec specification\n");
	break;
      }
#ifdef WITH_CURL
      case url_http:
      case url_https:
      case url_ftp: {
	error(0,"CURL database must have one db_spec specification %i\n",token);
	break;
      }
#endif
	
      default : {
	error(0,"db_readline_file_ram():Unknown or unsupported db in type.\n");
	
	break;
      }
      
      }
      return s;
    }
    
    /*
     * Here we read da spec
     */
    
    if (db_file_read_spec_ram(db)!=0) {
      /* somethin went wrong */
      return s;
    }
    
  }else {
    /* We need to switch the buffer cleanly*/
    db_buff(db,NULL);
  }

  s=(char**)malloc(sizeof(char*)*db_unknown);

  /* We NEED this to avoid Bus errors on Suns */
  for(i=0;i<db_unknown;i++){
    s[i]=NULL;
  }
  
  for(i=0;i<*db_osize;i++){
    switch (r=db_scan()) {
      
    case TDBSPEC : {
      
      error(0,"Database file can have only one db_spec.\nTrying to continue on line %li\n",*db_lineno);      
      break;
    }
    case TNAME : {
      if ((*db_order)[i]!=db_unknown) {
	s[*db_order[i]]=(char*)strdup(dbtext);
      }
      break;
    }
    
    case TID : {
      if ((*db_order)[i]!=db_unknown) {
	s[(*db_order)[i]]=(char*)strdup(dbtext);
      }
      break;
    }
    
    case TNEWLINE : {
      
      if (i==0) {
	i--;
	break;
      }
      if(gotend_db){
	return NULL;
      }
      /*  */

      error(0,"Not enough parameters in db:%li. Trying to continue.\n",
	    *db_lineno);
      for(a=0;a<i;a++){
	free(s[(*db_order)[a]]);
	s[(*db_order)[a]]=NULL;
      }
      i=0;
      break;

    }

    case TBEGIN_DB : {
      error(0,_("Corrupt db. Found @@begin_db inside db. Please check\n"));
      return NULL;
      break;
    }

    case TEND_DB : {
      gotend_db=1;
      token=db_scan();
      if(token!=TSTRING){
	error(0,_("Corrupt db. Checksum garbled\n"));
	abort();
      } else { /* FIXME: this probably isn't right */
#ifdef WITH_MHASH
	if(*md){
	  byte* dig=NULL;
	  char* digstr=NULL;
	  
	  *oldmdstr=strdup(dbtext);
	  
	  mhash(*md,NULL,0);
	  dig=(byte*)
	    malloc(sizeof(byte)*mhash_get_block_size(conf->dbhmactype));
	  mhash_deinit(*md,(void*)dig);
	  digstr=encode_base64(dig,mhash_get_block_size(conf->dbhmactype));
	  if(strncmp(digstr,*oldmdstr,strlen(digstr))!=0){
	    error(0,_("Db checksum mismatch for db:%i\n"),db);
	    abort();
	  }
	}
        else
        {
	  error(0,"@@end_db found without @@begin_db in db:%i\n",db);
	  abort();
	}
#endif
      }
      token=db_scan();
      if(token!=TNEWLINE){
	error(0,_("Corrupt db. Checksum garbled\n"));
	abort();
      }	
      break;
    }

    case TEND_DBNOMD : {
      gotend_db=1;
      if(FORCEDBMD){
        error(0,"Database %i does not have checksum!\n",db);
	abort();
      }
      break;
    }

    case TEOF : {
      if(gotend_db){
	return NULL;
      }	
      /* This can be the first token on a line */
      if(i>0){
	error(0,"Not enough parameters in db:%li\n",*db_lineno);
      };
      for(a=0;a<i;a++){
	free(s[(*db_order)[a]]);
      }
      free(s);
      return NULL;
      break;
    }
    case TERROR : {
      error(0,"There was an error in the database file on line:%li.\n",*db_lineno);
      break;
    }
    
    default : {
      
      error(0,"Not implemented in db_readline_file_ram %i\n\"%s\"",r,dbtext);
      
      free(s);
      s=NULL;
      i=*db_osize;
      break;
    }
    }
    
  }
  

  /*
   * If we don't get newline after reading all cells we print an error
   */
  a=db_scan();

  if (a!=TNEWLINE&&a!=TEOF) {
    error(0,"Newline expected in database. Reading until end of line\n");
    do {
      
      error(0,"Skipped value %s\n",dbtext);
      
      /*
       * Null statement
       */ 
      a=db_scan();
    }while(a!=TNEWLINE&&a!=TEOF);
    
  }
  
  return s;
  
}

int db_writechar_ram(char* s,FILE* file,int i)
{
  char* r=NULL;
  int retval=0;

  (void)file;
  
  if(i) {
    dofprintf_ram(" ");
  }

  if(s==NULL){
    retval=dofprintf_ram("0");
    return retval;
  }
  if(s[0]=='\0'){
    retval=dofprintf_ram("0-");
    return retval;
  }
  if(s[0]=='0'){
    retval=dofprintf_ram("00");
    if(retval<0){
      return retval;
    }
    s++;
  }
  
  if (!i && s[0]=='#') {
    dofprintf_ram("# ");
    r=CLEANDUP(s+1);
  } else {
    r=CLEANDUP(s);
  }
  
  retval=dofprintf_ram("%s",r);
  free(r);
  return retval;
}

int db_writeint_ram(long i,FILE* file,int a)
{
  (void)file;
  
  if(a) {
    dofprintf_ram(" ");
  }
  
  return dofprintf_ram("%li",i);
  
}
int db_writelong_ram(AIDE_OFF_TYPE i,FILE* file,int a)
{
  (void)file;
  
  if(a) {
    dofprintf_ram(" ");
  }
  
#if defined HAVE_OFF64_TYPE && SIZEOF_OFF64_T == SIZEOF_LONG_LONG || !defined HAVE_OFF64_TYPE && SIZEOF_OFF_T == SIZEOF_LONG_LONG
  return dofprintf_ram("%lli",(long long)i);
#else
  return dofprintf_ram("%li",i);
#endif
  
}

int db_write_byte_base64_ram(byte*data,size_t len,FILE* file,int i,
                         DB_ATTR_TYPE th, DB_ATTR_TYPE attr )
{
  char* tmpstr=NULL;
  int retval=0;
  
  (void)file;  
  if (data && !len)
    len = strlen((const char *)data);
  
  if (data!=NULL&&th&attr) {
    tmpstr=encode_base64(data,len);
  } else {
    tmpstr=NULL;
  }
  if(i){
    dofprintf_ram(" ");
  }

  if(tmpstr){
    retval=dofprintf_ram("%s", tmpstr);
    free(tmpstr);
    return retval;
  }else {
    return dofprintf_ram("0");
  }
  return 0;

}

int db_write_time_base64_ram(time_t i,FILE* file,int a)
{
  static char* ptr=NULL;
  char* tmpstr=NULL;
  int retval=0;

  (void)file;
  
  if(a){
    dofprintf_ram(" ");
  }

  if(i==0){
    retval=dofprintf_ram("0");
    return retval;
  }


  ptr=(char*)malloc(sizeof(char)*TIMEBUFSIZE);
  if (ptr==NULL) {
    error(0,"\nCannot allocate memory.\n");
    abort();
  }
  memset((void*)ptr,0,sizeof(char)*TIMEBUFSIZE);

  sprintf(ptr,"%li",i);


  tmpstr=encode_base64((byte *)ptr,strlen(ptr));
  retval=dofprintf_ram("%s", tmpstr);
  free(tmpstr);
  free(ptr);

  return retval;

}

int db_writeoct_ram(long i, FILE* file,int a)
{
  (void)file;
  
  if(a) {
    dofprintf_ram(" ");
  }
  
  return dofprintf_ram("%lo",i);
  
}

int db_writespec_file_ram(db_config* dbconf)
{
  int i=0;
  int j=0;
  int retval=1;
  void*key=NULL;
  int keylen=0;
  struct tm* st;
  time_t tim=time(&tim);
  st=localtime(&tim);

  retval=dofprintf_ram("@@begin_db\n");
  if(retval==0){
    return RETFAIL;
  }

#ifdef WITH_MHASH
  /* From hereon everything must MD'd before write to db */
  if((key=get_db_key())!=NULL){
    keylen=get_db_key_len();
    dbconf->do_dbnewmd=1;
    if( (dbconf->dbnewmd=
	 mhash_hmac_init(dbconf->dbhmactype,
			 key,
			 keylen,
			 mhash_get_hash_pblock(dbconf->dbhmactype)))==
	MHASH_FAILED){
      error(0, "mhash_hmac_init() failed for db write. Aborting\n");
      abort();
    }
  }
  
  
#endif

  if(dbconf->database_add_metadata) {
      retval=dofprintf_ram(
             "# This file was generated by Aide, version %s\n"
             "# Time of generation was %.4u-%.2u-%.2u %.2u:%.2u:%.2u\n",
             AIDEVERSION,
             st->tm_year+1900, st->tm_mon+1, st->tm_mday,
             st->tm_hour, st->tm_min, st->tm_sec
             );
      if(retval==0){
        return RETFAIL;
      }
  }
  if(dbconf->config_version){
    retval=dofprintf_ram(
		     "# The config version used to generate this file was:\n"
		     "# %s\n", dbconf->config_version);
    if(retval==0){
      return RETFAIL;
    }
  }
  retval=dofprintf_ram("@@db_spec ");
  if(retval==0){
    return RETFAIL;
  }
  for(i=0;i<dbconf->db_out_size;i++){
    for(j=0;j<db_unknown;j++){
      if((int)db_value[j]==(int)dbconf->db_out_order[i]){
	retval=dofprintf_ram("%s ",db_names[j]);
	if(retval==0){
	  return RETFAIL;
	}
	break;
      }
    }
  }
  retval=dofprintf_ram("\n");
  if(retval==0){
    return RETFAIL;
  }
  return RETOK;
}

#ifdef WITH_ACL
int db_writeacl_ram(acl_type* acl,FILE* file,int a)
{
#ifdef WITH_SUN_ACL
  int i;

  if(a) {
    dofprintf_ram(" ");
  }
  
  if (acl==NULL) {
    dofprintf_ram("0");
  } else {
    
    dofprintf_ram("%i",acl->entries);
    
    for (i=0;i<acl->entries;i++) {
      dofprintf_ram(",%i,%i,%i", acl->acl[i].a_type, acl->acl[i].a_id,
	      acl->acl[i].a_perm);
    }
  }
#endif
#ifdef WITH_POSIX_ACL
  if(a) {
    dofprintf_ram(" ");
  }
  
  if (acl==NULL) {
    dofprintf_ram("0");
  } else {    
    dofprintf_ram("POSIX"); /* This is _very_ incompatible */

    dofprintf_ram(",");
    if (acl->acl_a)
      db_write_byte_base64_ram((byte*)acl->acl_a, 0, file,0,1,1);
    else
      dofprintf_ram("0");
    dofprintf_ram(",");
    if (acl->acl_d)
      db_write_byte_base64_ram((byte*)acl->acl_d, 0, file,0,1,1);
    else
      dofprintf_ram("0");
  }
#endif
#ifndef WITH_ACL
  if(a) { /* compat. */
    dofprintf_ram(" ");
  }
  
  dofprintf_ram("0");
#endif
  
  return RETOK;
}
#endif

int db_writeline_file_ram(db_line* line,db_config* dbconf, url_t* url)
{
  int i;

  (void)url;
  
  for(i=0;i<dbconf->db_out_size;i++){
    switch (dbconf->db_out_order[i]) {
    case db_filename : {
      db_writechar_ram(line->filename,dbconf->db_out,i);
      break;
    }
    case db_linkname : {
      db_writechar_ram(line->linkname,dbconf->db_out,i);
      break;
    }
    case db_bcount : {
      db_writeint_ram(line->bcount,dbconf->db_out,i);
      break;
    }

    case db_mtime : {
      db_write_time_base64_ram(line->mtime,dbconf->db_out,i);
      break;
    }
    case db_atime : {
      db_write_time_base64_ram(line->atime,dbconf->db_out,i);
      break;
    }
    case db_ctime : {
      db_write_time_base64_ram(line->ctime,dbconf->db_out,i);
      break;
    }
    case db_inode : {
      db_writeint_ram(line->inode,dbconf->db_out,i);
      break;
    }
    case db_lnkcount : {
      db_writeint_ram(line->nlink,dbconf->db_out,i);
      break;
    }
    case db_uid : {
      db_writeint_ram(line->uid,dbconf->db_out,i);
      break;
    }
    case db_gid : {
      db_writeint_ram(line->gid,dbconf->db_out,i);
      break;
    }
    case db_size : {
      db_writelong_ram(line->size,dbconf->db_out,i);
      break;
    }
    case db_md5 : {
      db_write_byte_base64_ram(line->md5,
			   HASH_MD5_LEN,
			   dbconf->db_out,i,
			   DB_MD5,line->attr);
	
      break;
    }
    case db_sha1 : {
      db_write_byte_base64_ram(line->sha1,
			   HASH_SHA1_LEN,
			   dbconf->db_out,i,
			   DB_SHA1,line->attr);

      break;
    }
    case db_rmd160 : {
      db_write_byte_base64_ram(line->rmd160,
			   HASH_RMD160_LEN,
			   dbconf->db_out,i,
			   DB_RMD160,line->attr);
      break;
    }
    case db_tiger : {
      db_write_byte_base64_ram(line->tiger,
			   HASH_TIGER_LEN,
			   dbconf->db_out,i,
			   DB_TIGER,line->attr);
      break;
    }
    case db_perm : {
      db_writeoct_ram(line->perm,dbconf->db_out,i);
      break;
    }
    case db_crc32 : {
      db_write_byte_base64_ram(line->crc32,
			   HASH_CRC32_LEN,
			   dbconf->db_out,i,
			   DB_CRC32,line->attr);
      break;
    }
    case db_crc32b : {
      db_write_byte_base64_ram(line->crc32b,
			   HASH_CRC32B_LEN,
			   dbconf->db_out,i,
			   DB_CRC32B,line->attr);
      break;
    }
    case db_haval : {
      db_write_byte_base64_ram(line->haval,
			   HASH_HAVAL256_LEN,
			   dbconf->db_out,i,
			   DB_HAVAL,line->attr);
      break;
    }
    case db_gost : {
      db_write_byte_base64_ram(line->gost ,
			   HASH_GOST_LEN,
			   dbconf->db_out,i,
			   DB_GOST,line->attr);
      break;
    }
    case db_sha256 : {
      db_write_byte_base64_ram(line->sha256,
			   HASH_SHA256_LEN,
			   dbconf->db_out,i,
			   DB_SHA256,line->attr);

      break;
    }
    case db_sha512 : {
      db_write_byte_base64_ram(line->sha512,
			   HASH_SHA512_LEN,
			   dbconf->db_out,i,
			   DB_SHA512,line->attr);

      break;
    }
    case db_whirlpool : {
      db_write_byte_base64_ram(line->whirlpool,
			   HASH_WHIRLPOOL_LEN,
			   dbconf->db_out,i,
			   DB_WHIRLPOOL,line->attr);

      break;
    }
    case db_attr : {
      db_writelong_ram(line->attr, dbconf->db_out,i);
      break;
    }
#ifdef WITH_ACL
    case db_acl : {
      db_writeacl_ram(line->acl,dbconf->db_out,i);
      break;
    }
#endif
    case db_xattrs : {
        xattr_node *xattr = NULL;
        size_t num = 0;
        
        if (!line->xattrs)
        {
          db_writelong_ram(0, dbconf->db_out, i);
          break;
        }
        
        db_writelong_ram(line->xattrs->num, dbconf->db_out, i);
        
        xattr = line->xattrs->ents;
        while (num < line->xattrs->num)
        {
          dofprintf_ram(",");
          db_writechar_ram(xattr->key, dbconf->db_out, 0);
          dofprintf_ram(",");
          db_write_byte_base64_ram(xattr->val, xattr->vsz, dbconf->db_out, 0, 1, 1);
          
          ++xattr;
          ++num;
        }
      break;
    }
    case db_selinux : {
	db_write_byte_base64_ram((byte*)line->cntx, 0, dbconf->db_out, i, 1, 1);
      break;
    }
#ifdef WITH_E2FSATTRS
    case db_e2fsattrs : {
      db_writelong_ram(line->e2fsattrs,dbconf->db_out,i);
      break;
    }
#endif
    case db_checkmask : {
      db_writeoct_ram(line->attr,dbconf->db_out,i);
      break;
    }
    default : {
      error(0,"Not implemented in db_writeline_file_ram %i\n",
	    dbconf->db_out_order[i]);
      return RETFAIL;
    }
    
    }
    
  }

  dofprintf_ram("\n");
  /* Can't use fflush because of zlib.*/
  dofflush_ram();

  return RETOK;
}

int db_close_file_ram(db_config* dbconf)
{
  
#ifdef WITH_MHASH
  byte* dig=NULL;
  char* digstr=NULL;

  if(dbconf->db_out
#ifdef WITH_ZLIB
     || dbconf->db_gzout
#endif
     ){

    /* Let's write @@end_db <checksum> */
    if (dbconf->dbnewmd!=NULL) {
      mhash(dbconf->dbnewmd, NULL ,0);
      dig=(byte*)malloc(sizeof(byte)*mhash_get_block_size(dbconf->dbhmactype));
      mhash_deinit(dbconf->dbnewmd,(void*)dig);
      digstr=encode_base64(dig,mhash_get_block_size(dbconf->dbhmactype));
      dbconf->do_dbnewmd=0;
      dofprintf_ram("@@end_db %s\n",digstr);
      free(dig);
      free(digstr);
    } else {
      dofprintf_ram("@@end_db\n");
    }
  }
#endif

#ifndef WITH_ZLIB
  if(fclose(dbconf->db_out)){
    error(0,"Unable to close database:%s\n",strerror(errno));
    return RETFAIL;
  }
#else
  if(dbconf->gzip_dbout){
    if(gzclose(dbconf->db_gzout)){
      error(0,"Unable to close gzdatabase:%s\n",strerror(errno));
      return RETFAIL;
    }
  }else {
    if(fclose(dbconf->db_out)){
      error(0,"Unable to close database:%s\n",strerror(errno));
      return RETFAIL;
    }
  }
#endif

  return RETOK;
}
// vi: ts=8 sw=8
