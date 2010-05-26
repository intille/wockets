using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils.Filters
{
    public abstract class Filter
    {
        public Type _Type;
        public Order _Order;
        protected int order;

        public Filter(Type type, Order order)
        {
            _Type = type;
            _Order = order;
        }
    }
}
