package com.github.ackintosh.graphql.repository

import com.github.ackintosh.graphql.type.Recommend
import org.springframework.stereotype.Component

@Component
class RecommendRepository {
    // 取り急ぎデータはメモリに持っておくだけ
    private val recommends = mapOf(
            1 to Recommend(1, "テレワークにお役立ちのアイテム集合！"),
            2 to Recommend(2, "わけあり商品！")
    )

    fun all(): Collection<Recommend> {
        println("RecommendRepository::all()")
        return recommends.values
    }

    fun find(id: Int) : Recommend? {
        println("RecommendRepository::find()")
        return recommends[id]
    }
}