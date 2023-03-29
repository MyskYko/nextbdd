#ifndef NEXT_BDD_CACHE_H
#define NEXT_BDD_CACHE_H

#include <vector>
#include <iostream>
#include <iomanip>

#include "NextBddTypes.h"

namespace NextBdd {

  class Cache {
  public:
    Cache(int nCacheSizeLog, int nCacheMaxLog, int nVerbose);
    ~Cache();

    inline lit Lookup(lit x, lit y);
    inline void Insert(lit x, lit y, lit z);
    inline void Clear();
    inline void Resize();

  private:
    cac nSize;
    cac nMax;
    cac Mask;
    std::vector<lit> vCache;

    size nLookups;
    size nHits;
    size nThold;
    double HitRate;

    int nVerbose;
  };
  
  Cache::Cache(int nCacheSizeLog, int nCacheMaxLog, int nVerbose): nVerbose(nVerbose) {
    if(nCacheMaxLog < nCacheSizeLog)
      throw std::invalid_argument("nCacheMax must not be smaller than nCacheSize");
    nMax = (cac)1 << nCacheMaxLog;
    if(!(nMax << 1))
      throw std::length_error("Memout (nCacheMax) in init");
    nSize = (cac)1 << nCacheSizeLog;
    if(nVerbose)
      std::cout << "Allocating " << nSize << " cache entries" << std::endl;
    vCache.resize(nSize * 3);
    Mask = nSize - 1;
    nLookups = 0;
    nHits = 0;
    nThold = (nSize == nMax)? SizeMax(): nSize;
    HitRate = 1;
  }
  Cache::~Cache() {
    if(nVerbose)
      std::cout << "Free " << nSize << " cache entries" << std::endl;
  }

  inline lit Cache::Lookup(lit x, lit y) {
    nLookups++;
    if(nLookups > nThold) {
      double NewHitRate = (double)nHits / nLookups;
      if(nVerbose >= 2)
        std::cout << "Cache Hits: " << std::setw(10) << nHits << ", "
                  << "Lookups: " << std::setw(10) << nLookups << ", "
                  << "Rate: " << std::setw(10) << NewHitRate
                  << std::endl;
      if(NewHitRate > HitRate)
        Resize();
      if(nSize == nMax)
        nThold = SizeMax();
      else {
        nThold <<= 1;
        if(!nThold)
          nThold = SizeMax();
      }
      HitRate = NewHitRate;
    }
    cac i = (CacHash(x, y) & Mask) * 3;
    if(vCache[i] == x && vCache[i + 1] == y) {
      if(nVerbose >= 3)
        std::cout << "Cache hit: "
                  << "x = " << std::setw(10) << x << ", "
                  << "y = " << std::setw(10) << y << ", "
                  << "z = " << std::setw(10) << vCache[i + 2] << ", "
                  << "hash = " << std::hex << (CacHash(x, y) & Mask) << std::dec
                  << std::endl;
      nHits++;
      return vCache[i + 2];
    }
    return LitMax();
  }
  inline void Cache::Insert(lit x, lit y, lit z) {
    cac i = (CacHash(x, y) & Mask) * 3;
    vCache[i] = x;
    vCache[i + 1] = y;
    vCache[i + 2] = z;
    if(nVerbose >= 3)
      std::cout << "Cache ent: "
                << "x = " << std::setw(10) << x << ", "
                << "y = " << std::setw(10) << y << ", "
                << "z = " << std::setw(10) << z << ", "
                << "hash = " << std::hex << (CacHash(x, y) & Mask) << std::dec
                << std::endl;
  }
  inline void Cache::Clear() {
    std::fill(vCache.begin(), vCache.end(), 0);
  }
  inline void Cache::Resize() {
    cac nSizeOld = nSize;
    nSize <<= 1;
    if(nVerbose >= 2)
      std::cout << "Reallocating " << nSize << " cache entries" << std::endl;
    vCache.resize(nSize * 3);
    Mask = nSize - 1;
    for(cac j = 0; j < nSizeOld; j++) {
      cac i = j * 3;
      if(vCache[i] || vCache[i + 1]) {
        cac hash = (CacHash(vCache[i], vCache[i + 1]) & Mask) * 3;
        vCache[hash] = vCache[i];
        vCache[hash + 1] = vCache[i + 1];
        vCache[hash + 2] = vCache[i + 2];
        if(nVerbose >= 3)
          std::cout << "Cache mov: "
                    << "x = " << std::setw(10) << vCache[i] << ", "
                    << "y = " << std::setw(10) << vCache[i + 1] << ", "
                    << "z = " << std::setw(10) << vCache[i + 2] << ", "
                    << "hash = " << std::hex << (CacHash(vCache[i], vCache[i + 1]) & Mask) << std::dec
                    << std::endl;
      }
    }
  }

}

#endif
