import android
import semmle.code.java.TypeHierarchy
import semmle.code.java.dataflow.DataFlow

// Helper predicate to identify dynamic registrations
predicate isDynamicallyRegistered(Class c, string componentType) {
  exists(MethodAccess ma |
    (
      ma.getMethod().hasName("registerReceiver") and
      componentType = "Broadcast Receiver (Dynamic)" and
      DataFlow::localFlow(DataFlow::exprNode(c.getAConstructor().getAParameter()), DataFlow::exprNode(ma.getArgument(0)))
    ) or (
      ma.getMethod().hasName("registerService") and
      componentType = "Service (Dynamic)" and
      DataFlow::localFlow(DataFlow::exprNode(c.getAConstructor().getAParameter()), DataFlow::exprNode(ma.getArgument(1)))
    )
  )
}

from Class c, string componentType
where 
  // Static components
  (
    c.getASupertype+() instanceof TypeActivity and
    componentType = "Activity"
  ) or (
    c.getASupertype+() instanceof TypeContentProvider and
    componentType = "Content Provider"
  ) or (
    c.getASupertype+() instanceof TypeBroadcastReceiver and
    componentType = "Broadcast Receiver"
  ) or (
    c.getASupertype+() instanceof TypeService and
    componentType = "Service"
  ) or
  // Dynamic components
  isDynamicallyRegistered(c, componentType)
select componentType, c.getQualifiedName()
